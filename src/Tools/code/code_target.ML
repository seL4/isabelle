(*  Title:      Tools/code/code_target.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Serializer from intermediate language ("Thin-gol")
to target languages (like SML or Haskell).
*)

signature CODE_TARGET =
sig
  include BASIC_CODE_THINGOL;

  val add_syntax_class: string -> class
    -> (string * (string * string) list) option -> theory -> theory;
  val add_syntax_inst: string -> string * class -> bool -> theory -> theory;
  val add_syntax_tycoP: string -> string -> OuterParse.token list
    -> (theory -> theory) * OuterParse.token list;
  val add_syntax_constP: string -> string -> OuterParse.token list
    -> (theory -> theory) * OuterParse.token list;

  val add_undefined: string -> string -> string -> theory -> theory;
  val add_pretty_list: string -> string -> string -> theory -> theory;
  val add_pretty_list_string: string -> string -> string
    -> string -> string list -> theory -> theory;
  val add_pretty_char: string -> string -> string list -> theory -> theory
  val add_pretty_numeral: string -> bool -> bool -> string -> string -> string
    -> string -> string -> theory -> theory;
  val add_pretty_message: string -> string -> string list -> string
    -> string -> string -> theory -> theory;

  val allow_exception: string -> theory -> theory;

  type serialization;
  type serializer;
  val add_serializer: string * serializer -> theory -> theory;
  val assert_serializer: theory -> string -> string;
  val serialize: theory -> string -> bool -> string option -> Args.T list
    -> CodeThingol.code -> string list option -> serialization;
  val compile: serialization -> unit;
  val write: serialization -> unit;
  val file: Path.T -> serialization -> unit;
  val string: serialization -> string;
  val sml_of: theory -> CodeThingol.code -> string list -> string;
  val eval: theory -> (string * (unit -> 'a) option ref)
    -> CodeThingol.code -> CodeThingol.iterm * CodeThingol.itype -> string list -> 'a;
  val code_width: int ref;

  val setup: theory -> theory;
end;

structure CodeTarget : CODE_TARGET =
struct

open BasicCodeThingol;

(** basics **)

infixr 5 @@;
infixr 5 @|;
fun x @@ y = [x, y];
fun xs @| y = xs @ [y];
val str = PrintMode.setmp [] Pretty.str;
val concat = Pretty.block o Pretty.breaks;
val brackets = Pretty.enclose "(" ")" o Pretty.breaks;
fun semicolon ps = Pretty.block [concat ps, str ";"];
fun enum_default default sep opn cls [] = str default
  | enum_default default sep opn cls xs = Pretty.enum sep opn cls xs;

val code_width = ref 80;
fun code_source p = PrintMode.setmp [] (Pretty.setmp_margin (!code_width) Pretty.string_of) p ^ "\n";
fun code_writeln p = Pretty.setmp_margin (!code_width) Pretty.writeln p;


(** generic syntax **)

datatype lrx = L | R | X;

datatype fixity =
    BR
  | NOBR
  | INFX of (int * lrx);

val APP = INFX (~1, L);

fun fixity_lrx L L = false
  | fixity_lrx R R = false
  | fixity_lrx _ _ = true;

fun fixity NOBR NOBR = false
  | fixity BR NOBR = false
  | fixity NOBR BR = false
  | fixity (INFX (pr, lr)) (INFX (pr_ctxt, lr_ctxt)) =
      pr < pr_ctxt
      orelse pr = pr_ctxt
        andalso fixity_lrx lr lr_ctxt
      orelse pr_ctxt = ~1
  | fixity _ (INFX _) = false
  | fixity (INFX _) NOBR = false
  | fixity _ _ = true;

fun gen_brackify _ [p] = p
  | gen_brackify true (ps as _::_) = Pretty.enclose "(" ")" ps
  | gen_brackify false (ps as _::_) = Pretty.block ps;

fun brackify fxy_ctxt ps =
  gen_brackify (fixity BR fxy_ctxt) (Pretty.breaks ps);

fun brackify_infix infx fxy_ctxt ps =
  gen_brackify (fixity (INFX infx) fxy_ctxt) (Pretty.breaks ps);

type class_syntax = string * (string -> string option);
type typ_syntax = int * ((fixity -> itype -> Pretty.T)
  -> fixity -> itype list -> Pretty.T);
type term_syntax = int * ((CodeName.var_ctxt -> fixity -> iterm -> Pretty.T)
  -> CodeName.var_ctxt -> fixity -> (iterm * itype) list -> Pretty.T);


(** theory data **)

val target_diag = "diag";
val target_SML = "SML";
val target_OCaml = "OCaml";
val target_Haskell = "Haskell";

datatype syntax_expr = SyntaxExpr of {
  class: (string * (string -> string option)) Symtab.table,
  inst: unit Symtab.table,
  tyco: typ_syntax Symtab.table,
  const: term_syntax Symtab.table
};

fun mk_syntax_expr ((class, inst), (tyco, const)) =
  SyntaxExpr { class = class, inst = inst, tyco = tyco, const = const };
fun map_syntax_expr f (SyntaxExpr { class, inst, tyco, const }) =
  mk_syntax_expr (f ((class, inst), (tyco, const)));
fun merge_syntax_expr (SyntaxExpr { class = class1, inst = inst1, tyco = tyco1, const = const1 },
    SyntaxExpr { class = class2, inst = inst2, tyco = tyco2, const = const2 }) =
  mk_syntax_expr (
    (Symtab.join (K snd) (class1, class2),
       Symtab.join (K snd) (inst1, inst2)),
    (Symtab.join (K snd) (tyco1, tyco2),
       Symtab.join (K snd) (const1, const2))
  );

datatype serialization_dest = Compile | Write | File of Path.T | String;
type serialization = serialization_dest -> string option;

fun compile f = (f Compile; ());
fun write f = (f Write; ());
fun file p f = (f (File p); ());
fun string f = the (f String);

type serializer =
  string option
  -> Args.T list
  -> (string -> string)
  -> string list
  -> (string * Pretty.T) list
  -> (string -> string option)
  -> (string -> class_syntax option)
  -> (string -> typ_syntax option)
  -> (string -> term_syntax option)
  -> CodeThingol.code -> string list -> serialization;

datatype target = Target of {
  serial: serial,
  serializer: serializer,
  reserved: string list,
  includes: Pretty.T Symtab.table,
  syntax_expr: syntax_expr,
  module_alias: string Symtab.table
};

fun mk_target ((serial, serializer), ((reserved, includes), (syntax_expr, module_alias))) =
  Target { serial = serial, serializer = serializer, reserved = reserved, 
    includes = includes, syntax_expr = syntax_expr, module_alias = module_alias };
fun map_target f ( Target { serial, serializer, reserved, includes, syntax_expr, module_alias } ) =
  mk_target (f ((serial, serializer), ((reserved, includes), (syntax_expr, module_alias))));
fun merge_target target (Target { serial = serial1, serializer = serializer,
  reserved = reserved1, includes = includes1,
  syntax_expr = syntax_expr1, module_alias = module_alias1 },
    Target { serial = serial2, serializer = _,
      reserved = reserved2, includes = includes2,
      syntax_expr = syntax_expr2, module_alias = module_alias2 }) =
  if serial1 = serial2 then
    mk_target ((serial1, serializer),
      ((merge (op =) (reserved1, reserved2), Symtab.merge (op =) (includes1, includes2)),
        (merge_syntax_expr (syntax_expr1, syntax_expr2),
          Symtab.join (K snd) (module_alias1, module_alias2))
    ))
  else
    error ("Incompatible serializers: " ^ quote target);

structure CodeTargetData = TheoryDataFun
(
  type T = target Symtab.table * string list;
  val empty = (Symtab.empty, []);
  val copy = I;
  val extend = I;
  fun merge _ ((target1, exc1) : T, (target2, exc2)) =
    (Symtab.join merge_target (target1, target2), Library.merge (op =) (exc1, exc2));
);

fun the_serializer (Target { serializer, ... }) = serializer;
fun the_reserved (Target { reserved, ... }) = reserved;
fun the_includes (Target { includes, ... }) = includes;
fun the_syntax_expr (Target { syntax_expr = SyntaxExpr x, ... }) = x;
fun the_module_alias (Target { module_alias , ... }) = module_alias;

fun assert_serializer thy target =
  case Symtab.lookup (fst (CodeTargetData.get thy)) target
   of SOME data => target
    | NONE => error ("Unknown code target language: " ^ quote target);

fun add_serializer (target, seri) thy =
  let
    val _ = case Symtab.lookup (fst (CodeTargetData.get thy)) target
     of SOME _ => warning ("overwriting existing serializer " ^ quote target)
      | NONE => ();
  in
    thy
    |> (CodeTargetData.map o apfst oo Symtab.map_default)
          (target, mk_target ((serial (), seri), (([], Symtab.empty),
            (mk_syntax_expr ((Symtab.empty, Symtab.empty), (Symtab.empty, Symtab.empty)),
              Symtab.empty))))
          ((map_target o apfst o apsnd o K) seri)
  end;

fun map_seri_data target f thy =
  let
    val _ = assert_serializer thy target;
  in
    thy
    |> (CodeTargetData.map o apfst o Symtab.map_entry target o map_target) f
  end;

fun map_adaptions target =
  map_seri_data target o apsnd o apfst;
fun map_syntax_exprs target =
  map_seri_data target o apsnd o apsnd o apfst o map_syntax_expr;
fun map_module_alias target =
  map_seri_data target o apsnd o apsnd o apsnd;

fun get_serializer get_seri thy target permissive =
  let
    val (seris, exc) = CodeTargetData.get thy;
    val data = case Symtab.lookup seris target
     of SOME data => data
      | NONE => error ("Unknown code target language: " ^ quote target);
    val seri = get_seri data;
    val reserved = the_reserved data;
    val includes = Symtab.dest (the_includes data);
    val alias = the_module_alias data;
    val { class, inst, tyco, const } = the_syntax_expr data;
    val project = if target = target_diag then K I
      else CodeThingol.project_code permissive
        (Symtab.keys class @ Symtab.keys inst @ Symtab.keys tyco @ Symtab.keys const);
    fun check_empty_funs code = case filter_out (member (op =) exc)
        (CodeThingol.empty_funs code)
     of [] => code
      | names => error ("No defining equations for "
          ^ commas (map (CodeName.labelled_name thy) names));
  in fn module => fn args => fn code => fn cs =>
    seri module args (CodeName.labelled_name thy) reserved includes
      (Symtab.lookup alias) (Symtab.lookup class)
      (Symtab.lookup tyco) (Symtab.lookup const)
        ((check_empty_funs o project cs) code) (these cs)
  end;

val serialize = get_serializer the_serializer;

fun parse_args f args =
  case Scan.read Args.stopper f args
   of SOME x => x
    | NONE => error "Bad serializer arguments";


(** generic output combinators **)

(* applications and bindings *)

fun gen_pr_app pr_app' pr_term const_syntax labelled_name is_cons
      lhs vars fxy (app as ((c, (_, tys)), ts)) =
  case const_syntax c
   of NONE => if lhs andalso not (is_cons c) then
          error ("non-constructor on left hand side of equation: " ^ labelled_name c)
        else brackify fxy (pr_app' lhs vars app)
    | SOME (i, pr) =>
        let
          val k = if i < 0 then length tys else i;
          fun pr' fxy ts = pr (pr_term lhs) vars fxy (ts ~~ curry Library.take k tys);
        in if k = length ts
          then pr' fxy ts
        else if k < length ts
          then case chop k ts of (ts1, ts2) =>
            brackify fxy (pr' APP ts1 :: map (pr_term lhs vars BR) ts2)
          else pr_term lhs vars fxy (CodeThingol.eta_expand app k)
        end;

fun gen_pr_bind pr_bind' pr_term fxy ((v, pat), ty) vars =
  let
    val vs = case pat
     of SOME pat => CodeThingol.fold_varnames (insert (op =)) pat []
      | NONE => [];
    val vars' = CodeName.intro_vars (the_list v) vars;
    val vars'' = CodeName.intro_vars vs vars';
    val v' = Option.map (CodeName.lookup_var vars') v;
    val pat' = Option.map (pr_term true vars'' fxy) pat;
  in (pr_bind' ((v', pat'), ty), vars'') end;


(* list, char, string, numeral and monad abstract syntax transformations *)

fun implode_list c_nil c_cons t =
  let
    fun dest_cons (IConst (c, _) `$ t1 `$ t2) =
          if c = c_cons
          then SOME (t1, t2)
          else NONE
      | dest_cons _ = NONE;
    val (ts, t') = CodeThingol.unfoldr dest_cons t;
  in case t'
   of IConst (c, _) => if c = c_nil then SOME ts else NONE
    | _ => NONE
  end;

fun decode_char c_nibbles (IConst (c1, _), IConst (c2, _)) =
      let
        fun idx c = find_index (curry (op =) c) c_nibbles;
        fun decode ~1 _ = NONE
          | decode _ ~1 = NONE
          | decode n m = SOME (chr (n * 16 + m));
      in decode (idx c1) (idx c2) end
  | decode_char _ _ = NONE;

fun implode_string c_char c_nibbles mk_char mk_string ts =
  let
    fun implode_char (IConst (c, _) `$ t1 `$ t2) =
          if c = c_char then decode_char c_nibbles (t1, t2) else NONE
      | implode_char _ = NONE;
    val ts' = map implode_char ts;
  in if forall is_some ts'
    then (SOME o str o mk_string o implode o map_filter I) ts'
    else NONE
  end;

fun implode_numeral negative c_pls c_min c_bit0 c_bit1 =
  let
    fun dest_bit (IConst (c, _)) = if c = c_bit0 then 0
          else if c = c_bit1 then 1
          else error "Illegal numeral expression: illegal bit"
      | dest_bit _ = error "Illegal numeral expression: illegal bit";
    fun dest_numeral (IConst (c, _)) = if c = c_pls then SOME 0
          else if c = c_min then
            if negative then SOME ~1 else NONE
          else error "Illegal numeral expression: illegal leading digit"
      | dest_numeral (t1 `$ t2) =
          let val (n, b) = (dest_numeral t2, dest_bit t1)
          in case n of SOME n => SOME (2 * n + b) | NONE => NONE end
      | dest_numeral _ = error "Illegal numeral expression: illegal constant";
  in dest_numeral #> the_default 0 end;

fun implode_monad c_bind t =
  let
    fun dest_monad (IConst (c, _) `$ t1 `$ t2) =
          if c = c_bind
            then case CodeThingol.split_abs t2
             of SOME (((v, pat), ty), t') =>
                  SOME ((SOME (((SOME v, pat), ty), true), t1), t')
              | NONE => NONE
            else NONE
      | dest_monad t = case CodeThingol.split_let t
           of SOME (((pat, ty), tbind), t') =>
                SOME ((SOME (((NONE, SOME pat), ty), false), tbind), t')
            | NONE => NONE;
  in CodeThingol.unfoldr dest_monad t end;


(* name auxiliary *)

val first_upper = implode o nth_map 0 Symbol.to_ascii_upper o explode;
val first_lower = implode o nth_map 0 Symbol.to_ascii_lower o explode;

val dest_name =
  apfst NameSpace.implode o split_last o fst o split_last o NameSpace.explode;

fun mk_modl_name_tab init_names prefix module_alias code =
  let
    fun nsp_map f = NameSpace.explode #> map f #> NameSpace.implode;
    fun mk_alias name =
     case module_alias name
      of SOME name' => name'
       | NONE => nsp_map (fn name => (the_single o fst)
            (Name.variants [name] init_names)) name;
    fun mk_prefix name =
      case prefix
       of SOME prefix => NameSpace.append prefix name
        | NONE => name;
    val tab =
      Symtab.empty
      |> Graph.fold ((fn name => Symtab.default (name, (mk_alias #> mk_prefix) name))
           o fst o dest_name o fst)
             code
  in fn name => (the o Symtab.lookup tab) name end;



(** SML/OCaml serializer **)

datatype ml_def =
    MLFuns of (string * (typscheme * (iterm list * iterm) list)) list
  | MLDatas of (string * ((vname * sort) list * (string * itype list) list)) list
  | MLClass of string * (vname * ((class * string) list * (string * itype) list))
  | MLClassinst of string * ((class * (string * (vname * sort) list))
        * ((class * (string * (string * dict list list))) list
      * (string * const) list));

fun pr_sml tyco_syntax const_syntax labelled_name init_syms deresolv is_cons ml_def =
  let
    val pr_label_classrel = translate_string (fn "." => "__" | c => c)
      o NameSpace.qualifier;
    val pr_label_classparam = NameSpace.base o NameSpace.qualifier;
    fun pr_dicts fxy ds =
      let
        fun pr_dictvar (v, (_, 1)) = first_upper v ^ "_"
          | pr_dictvar (v, (i, _)) = first_upper v ^ string_of_int (i+1) ^ "_";
        fun pr_proj [] p =
              p
          | pr_proj [p'] p =
              brackets [p', p]
          | pr_proj (ps as _ :: _) p =
              brackets [Pretty.enum " o" "(" ")" ps, p];
        fun pr_dictc fxy (DictConst (inst, dss)) =
              brackify fxy ((str o deresolv) inst :: map (pr_dicts BR) dss)
          | pr_dictc fxy (DictVar (classrels, v)) =
              pr_proj (map (str o deresolv) classrels) ((str o pr_dictvar) v)
      in case ds
       of [] => str "()"
        | [d] => pr_dictc fxy d
        | _ :: _ => (Pretty.list "(" ")" o map (pr_dictc NOBR)) ds
      end;
    fun pr_tyvars vs =
      vs
      |> map (fn (v, sort) => map_index (fn (i, _) =>
           DictVar ([], (v, (i, length sort)))) sort)
      |> map (pr_dicts BR);
    fun pr_tycoexpr fxy (tyco, tys) =
      let
        val tyco' = (str o deresolv) tyco
      in case map (pr_typ BR) tys
       of [] => tyco'
        | [p] => Pretty.block [p, Pretty.brk 1, tyco']
        | (ps as _::_) => Pretty.block [Pretty.list "(" ")" ps, Pretty.brk 1, tyco']
      end
    and pr_typ fxy (tyco `%% tys) =
          (case tyco_syntax tyco
           of NONE => pr_tycoexpr fxy (tyco, tys)
            | SOME (i, pr) =>
                if not (i = length tys)
                then error ("Number of argument mismatch in customary serialization: "
                  ^ (string_of_int o length) tys ^ " given, "
                  ^ string_of_int i ^ " expected")
                else pr pr_typ fxy tys)
      | pr_typ fxy (ITyVar v) =
          str ("'" ^ v);
    fun pr_term lhs vars fxy (IConst c) =
          pr_app lhs vars fxy (c, [])
      | pr_term lhs vars fxy (IVar v) =
          str (CodeName.lookup_var vars v)
      | pr_term lhs vars fxy (t as t1 `$ t2) =
          (case CodeThingol.unfold_const_app t
           of SOME c_ts => pr_app lhs vars fxy c_ts
            | NONE =>
                brackify fxy [pr_term lhs vars NOBR t1, pr_term lhs vars BR t2])
      | pr_term lhs vars fxy (t as _ `|-> _) =
          let
            val (binds, t') = CodeThingol.unfold_abs t;
            fun pr ((v, pat), ty) =
              pr_bind NOBR ((SOME v, pat), ty)
              #>> (fn p => concat [str "fn", p, str "=>"]);
            val (ps, vars') = fold_map pr binds vars;
          in brackets (ps @ [pr_term lhs vars' NOBR t']) end
      | pr_term lhs vars fxy (ICase (cases as (_, t0))) =
          (case CodeThingol.unfold_const_app t0
           of SOME (c_ts as ((c, _), _)) => if is_none (const_syntax c)
                then pr_case vars fxy cases
                else pr_app lhs vars fxy c_ts
            | NONE => pr_case vars fxy cases)
    and pr_app' lhs vars (app as ((c, (iss, tys)), ts)) =
      if is_cons c then let
        val k = length tys
      in if k < 2 then 
        (str o deresolv) c :: map (pr_term lhs vars BR) ts
      else if k = length ts then
        [(str o deresolv) c, Pretty.enum "," "(" ")" (map (pr_term lhs vars NOBR) ts)]
      else [pr_term lhs vars BR (CodeThingol.eta_expand app k)] end else
        (str o deresolv) c
          :: (map (pr_dicts BR) o filter_out null) iss @ map (pr_term lhs vars BR) ts
    and pr_app lhs vars = gen_pr_app pr_app' pr_term const_syntax
      labelled_name is_cons lhs vars
    and pr_bind' ((NONE, NONE), _) = str "_"
      | pr_bind' ((SOME v, NONE), _) = str v
      | pr_bind' ((NONE, SOME p), _) = p
      | pr_bind' ((SOME v, SOME p), _) = concat [str v, str "as", p]
    and pr_bind fxy = gen_pr_bind pr_bind' pr_term fxy
    and pr_case vars fxy (cases as ((_, [_]), _)) =
          let
            val (binds, t') = CodeThingol.unfold_let (ICase cases);
            fun pr ((pat, ty), t) vars =
              vars
              |> pr_bind NOBR ((NONE, SOME pat), ty)
              |>> (fn p => semicolon [str "val", p, str "=", pr_term false vars NOBR t])
            val (ps, vars') = fold_map pr binds vars;
          in
            Pretty.chunks [
              [str ("let"), Pretty.fbrk, Pretty.chunks ps] |> Pretty.block,
              [str ("in"), Pretty.fbrk, pr_term false vars' NOBR t'] |> Pretty.block,
              str ("end")
            ]
          end
      | pr_case vars fxy (((td, ty), b::bs), _) =
          let
            fun pr delim (pat, t) =
              let
                val (p, vars') = pr_bind NOBR ((NONE, SOME pat), ty) vars;
              in
                concat [str delim, p, str "=>", pr_term false vars' NOBR t]
              end;
          in
            (Pretty.enclose "(" ")" o single o brackify fxy) (
              str "case"
              :: pr_term false vars NOBR td
              :: pr "of" b
              :: map (pr "|") bs
            )
          end
      | pr_case vars fxy ((_, []), _) = str "raise Fail \"empty case\""
    fun pr_def (MLFuns (funns as (funn :: funns'))) =
          let
            val definer =
              let
                fun no_args _ ((ts, _) :: _) = length ts
                  | no_args ty [] = (length o fst o CodeThingol.unfold_fun) ty;
                fun mk 0 [] = "val"
                  | mk 0 vs = if (null o filter_out (null o snd)) vs
                      then "val" else "fun"
                  | mk k _ = "fun";
                fun chk (_, ((vs, ty), eqs)) NONE = SOME (mk (no_args ty eqs) vs)
                  | chk (_, ((vs, ty), eqs)) (SOME defi) =
                      if defi = mk (no_args ty eqs) vs then SOME defi
                      else error ("Mixing simultaneous vals and funs not implemented: "
                        ^ commas (map (labelled_name o fst) funns));
              in the (fold chk funns NONE) end;
            fun pr_funn definer (name, ((raw_vs, ty), [])) =
                  let
                    val vs = filter_out (null o snd) raw_vs;
                    val n = length vs + (length o fst o CodeThingol.unfold_fun) ty;
                    val exc_str =
                      (ML_Syntax.print_string o NameSpace.base o NameSpace.qualifier) name;
                  in
                    concat (
                      str definer
                      :: (str o deresolv) name
                      :: map str (replicate n "_")
                      @ str "="
                      :: str "raise"
                      :: str "(Fail"
                      :: str exc_str
                      @@ str ")"
                    )
                  end
              | pr_funn definer (name, ((raw_vs, ty), eqs as eq :: eqs')) =
                  let
                    val vs = filter_out (null o snd) raw_vs;
                    val shift = if null eqs' then I else
                      map (Pretty.block o single o Pretty.block o single);
                    fun pr_eq definer (ts, t) =
                      let
                        val consts = map_filter
                          (fn c => if (is_some o const_syntax) c
                            then NONE else (SOME o NameSpace.base o deresolv) c)
                            ((fold o CodeThingol.fold_constnames) (insert (op =)) (t :: ts) []);
                        val vars = init_syms
                          |> CodeName.intro_vars consts
                          |> CodeName.intro_vars ((fold o CodeThingol.fold_unbound_varnames)
                               (insert (op =)) ts []);
                      in
                        concat (
                          [str definer, (str o deresolv) name]
                          @ (if null ts andalso null vs
                             then [str ":", pr_typ NOBR ty]
                             else
                               pr_tyvars vs
                               @ map (pr_term true vars BR) ts)
                       @ [str "=", pr_term false vars NOBR t]
                        )
                      end
                  in
                    (Pretty.block o Pretty.fbreaks o shift) (
                      pr_eq definer eq
                      :: map (pr_eq "|") eqs'
                    )
                  end;
            val (ps, p) = split_last (pr_funn definer funn :: map (pr_funn "and") funns');
          in Pretty.chunks (ps @ [Pretty.block ([p, str ";"])]) end
     | pr_def (MLDatas (datas as (data :: datas'))) =
          let
            fun pr_co (co, []) =
                  str (deresolv co)
              | pr_co (co, tys) =
                  concat [
                    str (deresolv co),
                    str "of",
                    Pretty.enum " *" "" "" (map (pr_typ (INFX (2, X))) tys)
                  ];
            fun pr_data definer (tyco, (vs, [])) =
                  concat (
                    str definer
                    :: pr_tycoexpr NOBR (tyco, map (ITyVar o fst) vs)
                    :: str "="
                    @@ str "EMPTY__" 
                  )
              | pr_data definer (tyco, (vs, cos)) =
                  concat (
                    str definer
                    :: pr_tycoexpr NOBR (tyco, map (ITyVar o fst) vs)
                    :: str "="
                    :: separate (str "|") (map pr_co cos)
                  );
            val (ps, p) = split_last
              (pr_data "datatype" data :: map (pr_data "and") datas');
          in Pretty.chunks (ps @ [Pretty.block ([p, str ";"])]) end
     | pr_def (MLClass (class, (v, (superclasses, classparams)))) =
          let
            val w = first_upper v ^ "_";
            fun pr_superclass_field (class, classrel) =
              (concat o map str) [
                pr_label_classrel classrel, ":", "'" ^ v, deresolv class
              ];
            fun pr_classparam_field (classparam, ty) =
              concat [
                (str o pr_label_classparam) classparam, str ":", pr_typ NOBR ty
              ];
            fun pr_classparam_proj (classparam, _) =
              semicolon [
                str "fun",
                (str o deresolv) classparam,
                Pretty.enclose "(" ")" [str (w ^ ":'" ^ v ^ " " ^ deresolv class)],
                str "=",
                str ("#" ^ pr_label_classparam classparam),
                str w
              ];
            fun pr_superclass_proj (_, classrel) =
              semicolon [
                str "fun",
                (str o deresolv) classrel,
                Pretty.enclose "(" ")" [str (w ^ ":'" ^ v ^ " " ^ deresolv class)],
                str "=",
                str ("#" ^ pr_label_classrel classrel),
                str w
              ];
          in
            Pretty.chunks (
              concat [
                str ("type '" ^ v),
                (str o deresolv) class,
                str "=",
                Pretty.enum "," "{" "};" (
                  map pr_superclass_field superclasses @ map pr_classparam_field classparams
                )
              ]
              :: map pr_superclass_proj superclasses
              @ map pr_classparam_proj classparams
            )
          end
     | pr_def (MLClassinst (inst, ((class, (tyco, arity)), (superarities, classparam_insts)))) =
          let
            fun pr_superclass (_, (classrel, dss)) =
              concat [
                (str o pr_label_classrel) classrel,
                str "=",
                pr_dicts NOBR [DictConst dss]
              ];
            fun pr_classparam (classparam, c_inst) =
              concat [
                (str o pr_label_classparam) classparam,
                str "=",
                pr_app false init_syms NOBR (c_inst, [])
              ];
          in
            semicolon ([
              str (if null arity then "val" else "fun"),
              (str o deresolv) inst ] @
              pr_tyvars arity @ [
              str "=",
              Pretty.enum "," "{" "}"
                (map pr_superclass superarities @ map pr_classparam classparam_insts),
              str ":",
              pr_tycoexpr NOBR (class, [tyco `%% map (ITyVar o fst) arity])
            ])
          end;
  in pr_def ml_def end;

fun pr_sml_modl name content =
  Pretty.chunks ([
    str ("structure " ^ name ^ " = "),
    str "struct",
    str ""
  ] @ content @ [
    str "",
    str ("end; (*struct " ^ name ^ "*)")
  ]);

fun pr_ocaml tyco_syntax const_syntax labelled_name
    init_syms deresolv is_cons ml_def =
  let
    fun pr_dicts fxy ds =
      let
        fun pr_dictvar (v, (_, 1)) = "_" ^ first_upper v
          | pr_dictvar (v, (i, _)) = "_" ^ first_upper v ^ string_of_int (i+1);
        fun pr_proj ps p =
          fold_rev (fn p2 => fn p1 => Pretty.block [p1, str ".", str p2]) ps p
        fun pr_dictc fxy (DictConst (inst, dss)) =
              brackify fxy ((str o deresolv) inst :: map (pr_dicts BR) dss)
          | pr_dictc fxy (DictVar (classrels, v)) =
              pr_proj (map deresolv classrels) ((str o pr_dictvar) v)
      in case ds
       of [] => str "()"
        | [d] => pr_dictc fxy d
        | _ :: _ => (Pretty.list "(" ")" o map (pr_dictc NOBR)) ds
      end;
    fun pr_tyvars vs =
      vs
      |> map (fn (v, sort) => map_index (fn (i, _) =>
           DictVar ([], (v, (i, length sort)))) sort)
      |> map (pr_dicts BR);
    fun pr_tycoexpr fxy (tyco, tys) =
      let
        val tyco' = (str o deresolv) tyco
      in case map (pr_typ BR) tys
       of [] => tyco'
        | [p] => Pretty.block [p, Pretty.brk 1, tyco']
        | (ps as _::_) => Pretty.block [Pretty.list "(" ")" ps, Pretty.brk 1, tyco']
      end
    and pr_typ fxy (tyco `%% tys) =
          (case tyco_syntax tyco
           of NONE => pr_tycoexpr fxy (tyco, tys)
            | SOME (i, pr) =>
                if not (i = length tys)
                then error ("Number of argument mismatch in customary serialization: "
                  ^ (string_of_int o length) tys ^ " given, "
                  ^ string_of_int i ^ " expected")
                else pr pr_typ fxy tys)
      | pr_typ fxy (ITyVar v) =
          str ("'" ^ v);
    fun pr_term lhs vars fxy (IConst c) =
          pr_app lhs vars fxy (c, [])
      | pr_term lhs vars fxy (IVar v) =
          str (CodeName.lookup_var vars v)
      | pr_term lhs vars fxy (t as t1 `$ t2) =
          (case CodeThingol.unfold_const_app t
           of SOME c_ts => pr_app lhs vars fxy c_ts
            | NONE =>
                brackify fxy [pr_term lhs vars NOBR t1, pr_term lhs vars BR t2])
      | pr_term lhs vars fxy (t as _ `|-> _) =
          let
            val (binds, t') = CodeThingol.unfold_abs t;
            fun pr ((v, pat), ty) = pr_bind BR ((SOME v, pat), ty);
            val (ps, vars') = fold_map pr binds vars;
          in brackets (str "fun" :: ps @ str "->" @@ pr_term lhs vars' NOBR t') end
      | pr_term lhs vars fxy (ICase (cases as (_, t0))) = (case CodeThingol.unfold_const_app t0
           of SOME (c_ts as ((c, _), _)) => if is_none (const_syntax c)
                then pr_case vars fxy cases
                else pr_app lhs vars fxy c_ts
            | NONE => pr_case vars fxy cases)
    and pr_app' lhs vars (app as ((c, (iss, tys)), ts)) =
      if is_cons c then
        if length tys = length ts
        then case ts
         of [] => [(str o deresolv) c]
          | [t] => [(str o deresolv) c, pr_term lhs vars BR t]
          | _ => [(str o deresolv) c, Pretty.enum "," "(" ")"
                    (map (pr_term lhs vars NOBR) ts)]
        else [pr_term lhs vars BR (CodeThingol.eta_expand app (length tys))]
      else (str o deresolv) c
        :: ((map (pr_dicts BR) o filter_out null) iss @ map (pr_term lhs vars BR) ts)
    and pr_app lhs vars = gen_pr_app pr_app' pr_term const_syntax
      labelled_name is_cons lhs vars
    and pr_bind' ((NONE, NONE), _) = str "_"
      | pr_bind' ((SOME v, NONE), _) = str v
      | pr_bind' ((NONE, SOME p), _) = p
      | pr_bind' ((SOME v, SOME p), _) = brackets [p, str "as", str v]
    and pr_bind fxy = gen_pr_bind pr_bind' pr_term fxy
    and pr_case vars fxy (cases as ((_, [_]), _)) =
          let
            val (binds, t') = CodeThingol.unfold_let (ICase cases);
            fun pr ((pat, ty), t) vars =
              vars
              |> pr_bind NOBR ((NONE, SOME pat), ty)
              |>> (fn p => concat
                  [str "let", p, str "=", pr_term false vars NOBR t, str "in"])
            val (ps, vars') = fold_map pr binds vars;
          in Pretty.chunks (ps @| pr_term false vars' NOBR t') end
      | pr_case vars fxy (((td, ty), b::bs), _) =
          let
            fun pr delim (pat, t) =
              let
                val (p, vars') = pr_bind NOBR ((NONE, SOME pat), ty) vars;
              in concat [str delim, p, str "->", pr_term false vars' NOBR t] end;
          in
            (Pretty.enclose "(" ")" o single o brackify fxy) (
              str "match"
              :: pr_term false vars NOBR td
              :: pr "with" b
              :: map (pr "|") bs
            )
          end
      | pr_case vars fxy ((_, []), _) = str "failwith \"empty case\"";
    fun pr_def (MLFuns (funns as funn :: funns')) =
          let
            fun fish_parm _ (w as SOME _) = w
              | fish_parm (IVar v) NONE = SOME v
              | fish_parm _ NONE = NONE;
            fun fillup_parm _ (_, SOME v) = v
              | fillup_parm x (i, NONE) = x ^ string_of_int i;
            fun fish_parms vars eqs =
              let
                val fished1 = fold (map2 fish_parm) eqs (replicate (length (hd eqs)) NONE);
                val x = Name.variant (map_filter I fished1) "x";
                val fished2 = map_index (fillup_parm x) fished1;
                val (fished3, _) = Name.variants fished2 Name.context;
                val vars' = CodeName.intro_vars fished3 vars;
              in map (CodeName.lookup_var vars') fished3 end;
            fun pr_eq (ts, t) =
              let
                val consts = map_filter
                  (fn c => if (is_some o const_syntax) c
                    then NONE else (SOME o NameSpace.base o deresolv) c)
                    ((fold o CodeThingol.fold_constnames) (insert (op =)) (t :: ts) []);
                val vars = init_syms
                  |> CodeName.intro_vars consts
                  |> CodeName.intro_vars ((fold o CodeThingol.fold_unbound_varnames)
                      (insert (op =)) ts []);
              in concat [
                (Pretty.block o Pretty.commas) (map (pr_term true vars NOBR) ts),
                str "->",
                pr_term false vars NOBR t
              ] end;
            fun pr_eqs name ty [] =
                  let
                    val n = (length o fst o CodeThingol.unfold_fun) ty;
                    val exc_str =
                      (ML_Syntax.print_string o NameSpace.base o NameSpace.qualifier) name;
                  in
                    concat (
                      map str (replicate n "_")
                      @ str "="
                      :: str "failwith"
                      @@ str exc_str
                    )
                  end
              | pr_eqs _ _ [(ts, t)] =
                  let
                    val consts = map_filter
                      (fn c => if (is_some o const_syntax) c
                        then NONE else (SOME o NameSpace.base o deresolv) c)
                        ((fold o CodeThingol.fold_constnames) (insert (op =)) (t :: ts) []);
                    val vars = init_syms
                      |> CodeName.intro_vars consts
                      |> CodeName.intro_vars ((fold o CodeThingol.fold_unbound_varnames)
                          (insert (op =)) ts []);
                  in
                    concat (
                      map (pr_term true vars BR) ts
                      @ str "="
                      @@ pr_term false vars NOBR t
                    )
                  end
              | pr_eqs _ _ (eqs as (eq as ([_], _)) :: eqs') =
                  Pretty.block (
                    str "="
                    :: Pretty.brk 1
                    :: str "function"
                    :: Pretty.brk 1
                    :: pr_eq eq
                    :: maps (append [Pretty.fbrk, str "|", Pretty.brk 1]
                          o single o pr_eq) eqs'
                  )
              | pr_eqs _ _ (eqs as eq :: eqs') =
                  let
                    val consts = map_filter
                      (fn c => if (is_some o const_syntax) c
                        then NONE else (SOME o NameSpace.base o deresolv) c)
                        ((fold o CodeThingol.fold_constnames)
                          (insert (op =)) (map snd eqs) []);
                    val vars = init_syms
                      |> CodeName.intro_vars consts;
                    val dummy_parms = (map str o fish_parms vars o map fst) eqs;
                  in
                    Pretty.block (
                      Pretty.breaks dummy_parms
                      @ Pretty.brk 1
                      :: str "="
                      :: Pretty.brk 1
                      :: str "match"
                      :: Pretty.brk 1
                      :: (Pretty.block o Pretty.commas) dummy_parms
                      :: Pretty.brk 1
                      :: str "with"
                      :: Pretty.brk 1
                      :: pr_eq eq
                      :: maps (append [Pretty.fbrk, str "|", Pretty.brk 1]
                           o single o pr_eq) eqs'
                    )
                  end;
            fun pr_funn definer (name, ((vs, ty), eqs)) =
              concat (
                str definer
                :: (str o deresolv) name
                :: pr_tyvars (filter_out (null o snd) vs)
                @| pr_eqs name ty eqs
              );
            val (ps, p) = split_last
              (pr_funn "let rec" funn :: map (pr_funn "and") funns');
          in Pretty.chunks (ps @ [Pretty.block ([p, str ";;"])]) end
     | pr_def (MLDatas (datas as (data :: datas'))) =
          let
            fun pr_co (co, []) =
                  str (deresolv co)
              | pr_co (co, tys) =
                  concat [
                    str (deresolv co),
                    str "of",
                    Pretty.enum " *" "" "" (map (pr_typ (INFX (2, X))) tys)
                  ];
            fun pr_data definer (tyco, (vs, [])) =
                  concat (
                    str definer
                    :: pr_tycoexpr NOBR (tyco, map (ITyVar o fst) vs)
                    :: str "="
                    @@ str "EMPTY_"
                  )
              | pr_data definer (tyco, (vs, cos)) =
                  concat (
                    str definer
                    :: pr_tycoexpr NOBR (tyco, map (ITyVar o fst) vs)
                    :: str "="
                    :: separate (str "|") (map pr_co cos)
                  );
            val (ps, p) = split_last
              (pr_data "type" data :: map (pr_data "and") datas');
          in Pretty.chunks (ps @ [Pretty.block ([p, str ";;"])]) end
     | pr_def (MLClass (class, (v, (superclasses, classparams)))) =
          let
            val w = "_" ^ first_upper v;
            fun pr_superclass_field (class, classrel) =
              (concat o map str) [
                deresolv classrel, ":", "'" ^ v, deresolv class
              ];
            fun pr_classparam_field (classparam, ty) =
              concat [
                (str o deresolv) classparam, str ":", pr_typ NOBR ty
              ];
            fun pr_classparam_proj (classparam, _) =
              concat [
                str "let",
                (str o deresolv) classparam,
                str w,
                str "=",
                str (w ^ "." ^ deresolv classparam ^ ";;")
              ];
          in Pretty.chunks (
            concat [
              str ("type '" ^ v),
              (str o deresolv) class,
              str "=",
              enum_default "();;" ";" "{" "};;" (
                map pr_superclass_field superclasses
                @ map pr_classparam_field classparams
              )
            ]
            :: map pr_classparam_proj classparams
          ) end
     | pr_def (MLClassinst (inst, ((class, (tyco, arity)), (superarities, classparam_insts)))) =
          let
            fun pr_superclass (_, (classrel, dss)) =
              concat [
                (str o deresolv) classrel,
                str "=",
                pr_dicts NOBR [DictConst dss]
              ];
            fun pr_classparam_inst (classparam, c_inst) =
              concat [
                (str o deresolv) classparam,
                str "=",
                pr_app false init_syms NOBR (c_inst, [])
              ];
          in
            concat (
              str "let"
              :: (str o deresolv) inst
              :: pr_tyvars arity
              @ str "="
              @@ (Pretty.enclose "(" ");;" o Pretty.breaks) [
                enum_default "()" ";" "{" "}" (map pr_superclass superarities
                  @ map pr_classparam_inst classparam_insts),
                str ":",
                pr_tycoexpr NOBR (class, [tyco `%% map (ITyVar o fst) arity])
              ]
            )
          end;
  in pr_def ml_def end;

fun pr_ocaml_modl name content =
  Pretty.chunks ([
    str ("module " ^ name ^ " = "),
    str "struct",
    str ""
  ] @ content @ [
    str "",
    str ("end;; (*struct " ^ name ^ "*)")
  ]);

fun seri_ml internal output_cont pr_def pr_modl module labelled_name reserved_syms includes raw_module_alias
  (_ : string -> class_syntax option) tyco_syntax const_syntax code cs seri_dest =
  let
    val module_alias = if is_some module then K module else raw_module_alias;
    val is_cons = CodeThingol.is_cons code;
    datatype node =
        Def of string * ml_def option
      | Module of string * ((Name.context * Name.context) * node Graph.T);
    val init_names = Name.make_context reserved_syms;
    val init_module = ((init_names, init_names), Graph.empty);
    fun map_node [] f = f
      | map_node (m::ms) f =
          Graph.default_node (m, Module (m, init_module))
          #> Graph.map_node m (fn (Module (dmodlname, (nsp, nodes))) =>
               Module (dmodlname, (nsp, map_node ms f nodes)));
    fun map_nsp_yield [] f (nsp, nodes) =
          let
            val (x, nsp') = f nsp
          in (x, (nsp', nodes)) end
      | map_nsp_yield (m::ms) f (nsp, nodes) =
          let
            val (x, nodes') =
              nodes
              |> Graph.default_node (m, Module (m, init_module))
              |> Graph.map_node_yield m (fn Module (dmodlname, nsp_nodes) => 
                  let
                    val (x, nsp_nodes') = map_nsp_yield ms f nsp_nodes
                  in (x, Module (dmodlname, nsp_nodes')) end)
          in (x, (nsp, nodes')) end;
    val init_syms = CodeName.make_vars reserved_syms;
    val name_modl = mk_modl_name_tab init_names NONE module_alias code;
    fun name_def upper name nsp =
      let
        val (_, base) = dest_name name;
        val base' = if upper then first_upper base else base;
        val ([base''], nsp') = Name.variants [base'] nsp;
      in (base'', nsp') end;
    fun map_nsp_fun f (nsp_fun, nsp_typ) =
      let
        val (x, nsp_fun') = f nsp_fun
      in (x, (nsp_fun', nsp_typ)) end;
    fun map_nsp_typ f (nsp_fun, nsp_typ) =
      let
        val (x, nsp_typ') = f nsp_typ
      in (x, (nsp_fun, nsp_typ')) end;
    fun mk_funs defs =
      fold_map
        (fn (name, CodeThingol.Fun info) =>
              map_nsp_fun (name_def false name) >>
                (fn base => (base, (name, (apsnd o map) fst info)))
          | (name, def) =>
              error ("Function block containing illegal definition: " ^ labelled_name name)
        ) defs
      >> (split_list #> apsnd MLFuns);
    fun mk_datatype defs =
      fold_map
        (fn (name, CodeThingol.Datatype info) =>
              map_nsp_typ (name_def false name) >> (fn base => (base, SOME (name, info)))
          | (name, CodeThingol.Datatypecons _) =>
              map_nsp_fun (name_def true name) >> (fn base => (base, NONE))
          | (name, def) =>
              error ("Datatype block containing illegal definition: " ^ labelled_name name)
        ) defs
      >> (split_list #> apsnd (map_filter I
        #> (fn [] => error ("Datatype block without data definition: "
                  ^ (commas o map (labelled_name o fst)) defs)
             | infos => MLDatas infos)));
    fun mk_class defs =
      fold_map
        (fn (name, CodeThingol.Class info) =>
              map_nsp_typ (name_def false name) >> (fn base => (base, SOME (name, info)))
          | (name, CodeThingol.Classrel _) =>
              map_nsp_fun (name_def false name) >> (fn base => (base, NONE))
          | (name, CodeThingol.Classparam _) =>
              map_nsp_fun (name_def false name) >> (fn base => (base, NONE))
          | (name, def) =>
              error ("Class block containing illegal definition: " ^ labelled_name name)
        ) defs
      >> (split_list #> apsnd (map_filter I
        #> (fn [] => error ("Class block without class definition: "
                  ^ (commas o map (labelled_name o fst)) defs)
             | [info] => MLClass info)));
    fun mk_inst [(name, CodeThingol.Classinst info)] =
      map_nsp_fun (name_def false name)
      >> (fn base => ([base], MLClassinst (name, (apsnd o apsnd o map) fst info)));
    fun add_group mk defs nsp_nodes =
      let
        val names as (name :: names') = map fst defs;
        val deps =
          []
          |> fold (fold (insert (op =)) o Graph.imm_succs code) names
          |> subtract (op =) names;
        val (modls, _) = (split_list o map dest_name) names;
        val modl' = (the_single o distinct (op =) o map name_modl) modls
          handle Empty =>
            error ("Different namespace prefixes for mutual dependencies:\n"
              ^ commas (map labelled_name names)
              ^ "\n"
              ^ commas (map (NameSpace.qualifier o NameSpace.qualifier) names));
        val modl_explode = NameSpace.explode modl';
        fun add_dep name name'' =
          let
            val modl'' = (name_modl o fst o dest_name) name'';
          in if modl' = modl'' then
            map_node modl_explode
              (Graph.add_edge (name, name''))
          else let
            val (common, (diff1::_, diff2::_)) = chop_prefix (op =)
              (modl_explode, NameSpace.explode modl'');
          in
            map_node common
              (fn gr => Graph.add_edge_acyclic (diff1, diff2) gr
                handle Graph.CYCLES _ => error ("Dependency "
                  ^ quote name ^ " -> " ^ quote name''
                  ^ " would result in module dependency cycle"))
          end end;
      in
        nsp_nodes
        |> map_nsp_yield modl_explode (mk defs)
        |-> (fn (base' :: bases', def') =>
           apsnd (map_node modl_explode (Graph.new_node (name, (Def (base', SOME def')))
              #> fold2 (fn name' => fn base' =>
                   Graph.new_node (name', (Def (base', NONE)))) names' bases')))
        |> apsnd (fold (fn name => fold (add_dep name) deps) names)
        |> apsnd (fold_product (curry (map_node modl_explode o Graph.add_edge)) names names)
      end;
    fun group_defs [(_, CodeThingol.Bot)] =
          I
      | group_defs ((defs as (_, CodeThingol.Fun _)::_)) =
          add_group mk_funs defs
      | group_defs ((defs as (_, CodeThingol.Datatypecons _)::_)) =
          add_group mk_datatype defs
      | group_defs ((defs as (_, CodeThingol.Datatype _)::_)) =
          add_group mk_datatype defs
      | group_defs ((defs as (_, CodeThingol.Class _)::_)) =
          add_group mk_class defs
      | group_defs ((defs as (_, CodeThingol.Classrel _)::_)) =
          add_group mk_class defs
      | group_defs ((defs as (_, CodeThingol.Classparam _)::_)) =
          add_group mk_class defs
      | group_defs ((defs as [(_, CodeThingol.Classinst _)])) =
          add_group mk_inst defs
      | group_defs defs = error ("Illegal mutual dependencies: " ^
          (commas o map (labelled_name o fst)) defs)
    val (_, nodes) =
      init_module
      |> fold group_defs (map (AList.make (Graph.get_node code))
          (rev (Graph.strong_conn code)))
    fun deresolver prefix name = 
      let
        val modl = (fst o dest_name) name;
        val modl' = (NameSpace.explode o name_modl) modl;
        val (_, (_, remainder)) = chop_prefix (op =) (prefix, modl');
        val defname' =
          nodes
          |> fold (fn m => fn g => case Graph.get_node g m
              of Module (_, (_, g)) => g) modl'
          |> (fn g => case Graph.get_node g name of Def (defname, _) => defname);
      in
        NameSpace.implode (remainder @ [defname'])
      end handle Graph.UNDEF _ =>
        error ("Unknown definition name: " ^ labelled_name name);
    fun pr_node prefix (Def (_, NONE)) =
          NONE
      | pr_node prefix (Def (_, SOME def)) =
          SOME (pr_def tyco_syntax const_syntax labelled_name init_syms
            (deresolver prefix) is_cons def)
      | pr_node prefix (Module (dmodlname, (_, nodes))) =
          SOME (pr_modl dmodlname (
            separate (str "")
                ((map_filter (pr_node (prefix @ [dmodlname]) o Graph.get_node nodes)
                o rev o flat o Graph.strong_conn) nodes)));
    val p = Pretty.chunks (separate (str "") (map snd includes @ (map_filter
      (pr_node [] o Graph.get_node nodes) o rev o flat o Graph.strong_conn) nodes));
    val deresolv = try (deresolver (if is_some module then the_list module else []));
    val output = case seri_dest
     of Compile => K NONE o internal o code_source
      | Write => K NONE o code_writeln
      | File file => K NONE o File.write file o code_source
      | String => SOME o code_source;
  in output_cont (map_filter deresolv cs, output p) end;

fun isar_seri_sml module =
  parse_args (Scan.succeed ())
  #> (fn () => seri_ml (use_text (1, "generated code") Output.ml_output false) snd pr_sml pr_sml_modl module);

fun isar_seri_ocaml module =
  parse_args (Scan.succeed ())
  #> (fn () => seri_ml (fn _ => error "OCaml: no internal compilation") snd pr_ocaml pr_ocaml_modl module)


(** Haskell serializer **)

local

fun pr_bind' ((NONE, NONE), _) = str "_"
  | pr_bind' ((SOME v, NONE), _) = str v
  | pr_bind' ((NONE, SOME p), _) = p
  | pr_bind' ((SOME v, SOME p), _) = brackets [str v, str "@", p]

val pr_bind_haskell = gen_pr_bind pr_bind';

in

fun pr_haskell class_syntax tyco_syntax const_syntax labelled_name
    init_syms deresolv_here deresolv is_cons contr_classparam_typs deriving_show def =
  let
    fun class_name class = case class_syntax class
     of NONE => deresolv class
      | SOME (class, _) => class;
    fun classparam_name class classparam = case class_syntax class
     of NONE => deresolv_here classparam
      | SOME (_, classparam_syntax) => case classparam_syntax classparam
         of NONE => (snd o dest_name) classparam
          | SOME classparam => classparam;
    fun pr_typcontext tyvars vs = case maps (fn (v, sort) => map (pair v) sort) vs
     of [] => []
      | classbinds => Pretty.enum "," "(" ")" (
          map (fn (v, class) =>
            str (class_name class ^ " " ^ CodeName.lookup_var tyvars v)) classbinds)
          @@ str " => ";
    fun pr_typforall tyvars vs = case map fst vs
     of [] => []
      | vnames => str "forall " :: Pretty.breaks
          (map (str o CodeName.lookup_var tyvars) vnames) @ str "." @@ Pretty.brk 1;
    fun pr_tycoexpr tyvars fxy (tyco, tys) =
      brackify fxy (str tyco :: map (pr_typ tyvars BR) tys)
    and pr_typ tyvars fxy (tycoexpr as tyco `%% tys) =
          (case tyco_syntax tyco
           of NONE =>
                pr_tycoexpr tyvars fxy (deresolv tyco, tys)
            | SOME (i, pr) =>
                if not (i = length tys)
                then error ("Number of argument mismatch in customary serialization: "
                  ^ (string_of_int o length) tys ^ " given, "
                  ^ string_of_int i ^ " expected")
                else pr (pr_typ tyvars) fxy tys)
      | pr_typ tyvars fxy (ITyVar v) =
          (str o CodeName.lookup_var tyvars) v;
    fun pr_typdecl tyvars (vs, tycoexpr) =
      Pretty.block (pr_typcontext tyvars vs @| pr_tycoexpr tyvars NOBR tycoexpr);
    fun pr_typscheme tyvars (vs, ty) =
      Pretty.block (pr_typforall tyvars vs @ pr_typcontext tyvars vs @| pr_typ tyvars NOBR ty);
    fun pr_term tyvars lhs vars fxy (IConst c) =
          pr_app tyvars lhs vars fxy (c, [])
      | pr_term tyvars lhs vars fxy (t as (t1 `$ t2)) =
          (case CodeThingol.unfold_const_app t
           of SOME app => pr_app tyvars lhs vars fxy app
            | _ =>
                brackify fxy [
                  pr_term tyvars lhs vars NOBR t1,
                  pr_term tyvars lhs vars BR t2
                ])
      | pr_term tyvars lhs vars fxy (IVar v) =
          (str o CodeName.lookup_var vars) v
      | pr_term tyvars lhs vars fxy (t as _ `|-> _) =
          let
            val (binds, t') = CodeThingol.unfold_abs t;
            fun pr ((v, pat), ty) = pr_bind tyvars BR ((SOME v, pat), ty);
            val (ps, vars') = fold_map pr binds vars;
          in brackets (str "\\" :: ps @ str "->" @@ pr_term tyvars lhs vars' NOBR t') end
      | pr_term tyvars lhs vars fxy (ICase (cases as (_, t0))) =
          (case CodeThingol.unfold_const_app t0
           of SOME (c_ts as ((c, _), _)) => if is_none (const_syntax c)
                then pr_case tyvars vars fxy cases
                else pr_app tyvars lhs vars fxy c_ts
            | NONE => pr_case tyvars vars fxy cases)
    and pr_app' tyvars lhs vars ((c, (_, tys)), ts) = case contr_classparam_typs c
     of [] => (str o deresolv) c :: map (pr_term tyvars lhs vars BR) ts
      | fingerprint => let
          val ts_fingerprint = ts ~~ curry Library.take (length ts) fingerprint;
          val needs_annotation = forall (fn (_, NONE) => true | (t, SOME _) =>
            (not o CodeThingol.locally_monomorphic) t) ts_fingerprint;
          fun pr_term_anno (t, NONE) _ = pr_term tyvars lhs vars BR t
            | pr_term_anno (t, SOME _) ty =
                brackets [pr_term tyvars lhs vars NOBR t, str "::", pr_typ tyvars NOBR ty];
        in
          if needs_annotation then
            (str o deresolv) c :: map2 pr_term_anno ts_fingerprint (curry Library.take (length ts) tys)
          else (str o deresolv) c :: map (pr_term tyvars lhs vars BR) ts
        end
    and pr_app tyvars lhs vars  = gen_pr_app (pr_app' tyvars) (pr_term tyvars) const_syntax
      labelled_name is_cons lhs vars
    and pr_bind tyvars = pr_bind_haskell (pr_term tyvars)
    and pr_case tyvars vars fxy (cases as ((_, [_]), _)) =
          let
            val (binds, t) = CodeThingol.unfold_let (ICase cases);
            fun pr ((pat, ty), t) vars =
              vars
              |> pr_bind tyvars BR ((NONE, SOME pat), ty)
              |>> (fn p => semicolon [p, str "=", pr_term tyvars false vars NOBR t])
            val (ps, vars') = fold_map pr binds vars;
          in
            Pretty.block_enclose (
              str "let {",
              concat [str "}", str "in", pr_term tyvars false vars' NOBR t]
            ) ps
          end
      | pr_case tyvars vars fxy (((td, ty), bs as _ :: _), _) =
          let
            fun pr (pat, t) =
              let
                val (p, vars') = pr_bind tyvars NOBR ((NONE, SOME pat), ty) vars;
              in semicolon [p, str "->", pr_term tyvars false vars' NOBR t] end;
          in
            Pretty.block_enclose (
              concat [str "(case", pr_term tyvars false vars NOBR td, str "of", str "{"],
              str "})"
            ) (map pr bs)
          end
      | pr_case tyvars vars fxy ((_, []), _) = str "error \"empty case\"";
    fun pr_def (name, CodeThingol.Fun ((vs, ty), [])) =
          let
            val tyvars = CodeName.intro_vars (map fst vs) init_syms;
            val n = (length o fst o CodeThingol.unfold_fun) ty;
          in
            Pretty.chunks [
              Pretty.block [
                (str o suffix " ::" o deresolv_here) name,
                Pretty.brk 1,
                pr_typscheme tyvars (vs, ty),
                str ";"
              ],
              concat (
                (str o deresolv_here) name
                :: map str (replicate n "_")
                @ str "="
                :: str "error"
                @@ (str o (fn s => s ^ ";") o ML_Syntax.print_string
                    o NameSpace.base o NameSpace.qualifier) name
              )
            ]
          end
      | pr_def (name, CodeThingol.Fun ((vs, ty), eqs)) =
          let
            val tyvars = CodeName.intro_vars (map fst vs) init_syms;
            fun pr_eq ((ts, t), _) =
              let
                val consts = map_filter
                  (fn c => if (is_some o const_syntax) c
                    then NONE else (SOME o NameSpace.base o deresolv) c)
                    ((fold o CodeThingol.fold_constnames) (insert (op =)) (t :: ts) []);
                val vars = init_syms
                  |> CodeName.intro_vars consts
                  |> CodeName.intro_vars ((fold o CodeThingol.fold_unbound_varnames)
                       (insert (op =)) ts []);
              in
                semicolon (
                  (str o deresolv_here) name
                  :: map (pr_term tyvars true vars BR) ts
                  @ str "="
                  @@ pr_term tyvars false vars NOBR t
                )
              end;
          in
            Pretty.chunks (
              Pretty.block [
                (str o suffix " ::" o deresolv_here) name,
                Pretty.brk 1,
                pr_typscheme tyvars (vs, ty),
                str ";"
              ]
              :: map pr_eq eqs
            )
          end
      | pr_def (name, CodeThingol.Datatype (vs, [])) =
          let
            val tyvars = CodeName.intro_vars (map fst vs) init_syms;
          in
            semicolon [
              str "data",
              pr_typdecl tyvars (vs, (deresolv_here name, map (ITyVar o fst) vs))
            ]
          end
      | pr_def (name, CodeThingol.Datatype (vs, [(co, [ty])])) =
          let
            val tyvars = CodeName.intro_vars (map fst vs) init_syms;
          in
            semicolon (
              str "newtype"
              :: pr_typdecl tyvars (vs, (deresolv_here name, map (ITyVar o fst) vs))
              :: str "="
              :: (str o deresolv_here) co
              :: pr_typ tyvars BR ty
              :: (if deriving_show name then [str "deriving (Read, Show)"] else [])
            )
          end
      | pr_def (name, CodeThingol.Datatype (vs, co :: cos)) =
          let
            val tyvars = CodeName.intro_vars (map fst vs) init_syms;
            fun pr_co (co, tys) =
              concat (
                (str o deresolv_here) co
                :: map (pr_typ tyvars BR) tys
              )
          in
            semicolon (
              str "data"
              :: pr_typdecl tyvars (vs, (deresolv_here name, map (ITyVar o fst) vs))
              :: str "="
              :: pr_co co
              :: map ((fn p => Pretty.block [str "| ", p]) o pr_co) cos
              @ (if deriving_show name then [str "deriving (Read, Show)"] else [])
            )
          end
      | pr_def (name, CodeThingol.Class (v, (superclasses, classparams))) =
          let
            val tyvars = CodeName.intro_vars [v] init_syms;
            fun pr_classparam (classparam, ty) =
              semicolon [
                (str o classparam_name name) classparam,
                str "::",
                pr_typ tyvars NOBR ty
              ]
          in
            Pretty.block_enclose (
              Pretty.block [
                str "class ",
                Pretty.block (pr_typcontext tyvars [(v, map fst superclasses)]),
                str (deresolv_here name ^ " " ^ CodeName.lookup_var tyvars v),
                str " where {"
              ],
              str "};"
            ) (map pr_classparam classparams)
          end
      | pr_def (_, CodeThingol.Classinst ((class, (tyco, vs)), (_, classparam_insts))) =
          let
            val tyvars = CodeName.intro_vars (map fst vs) init_syms;
            fun pr_instdef ((classparam, c_inst), _) =
              semicolon [
                (str o classparam_name class) classparam,
                str "=",
                pr_app tyvars false init_syms NOBR (c_inst, [])
              ];
          in
            Pretty.block_enclose (
              Pretty.block [
                str "instance ",
                Pretty.block (pr_typcontext tyvars vs),
                str (class_name class ^ " "),
                pr_typ tyvars BR (tyco `%% map (ITyVar o fst) vs),
                str " where {"
              ],
              str "};"
            ) (map pr_instdef classparam_insts)
          end;
  in pr_def def end;

fun pretty_haskell_monad c_bind =
  let
    fun pretty pr vars fxy [(t, _)] =
      let
        val pr_bind = pr_bind_haskell (K pr);
        fun pr_monad (NONE, t) vars =
              (semicolon [pr vars NOBR t], vars)
          | pr_monad (SOME (bind, true), t) vars = vars
              |> pr_bind NOBR bind
              |>> (fn p => semicolon [p, str "<-", pr vars NOBR t])
          | pr_monad (SOME (bind, false), t) vars = vars
              |> pr_bind NOBR bind
              |>> (fn p => semicolon [str "let", p, str "=", pr vars NOBR t]);
        val (binds, t) = implode_monad c_bind t;
        val (ps, vars') = fold_map pr_monad binds vars;
        fun brack p = if fixity BR fxy then Pretty.block [str "(", p, str ")"] else p;
      in (brack o Pretty.block_enclose (str "do {", str "}")) (ps @| pr vars' NOBR t) end;
  in (1, pretty) end;

end; (*local*)

fun seri_haskell module_prefix module string_classes labelled_name
    reserved_syms includes raw_module_alias
    class_syntax tyco_syntax const_syntax code cs seri_dest =
  let
    val is_cons = CodeThingol.is_cons code;
    val contr_classparam_typs = CodeThingol.contr_classparam_typs code;
    val module_alias = if is_some module then K module else raw_module_alias;
    val init_names = Name.make_context reserved_syms;
    val name_modl = mk_modl_name_tab init_names module_prefix module_alias code;
    fun add_def (name, (def, deps)) =
      let
        val (modl, base) = dest_name name;
        val name_def = yield_singleton Name.variants;
        fun add_fun upper (nsp_fun, nsp_typ) =
          let
            val (base', nsp_fun') =
              name_def (if upper then first_upper base else base) nsp_fun
          in (base', (nsp_fun', nsp_typ)) end;
        fun add_typ (nsp_fun, nsp_typ) =
          let
            val (base', nsp_typ') = name_def (first_upper base) nsp_typ
          in (base', (nsp_fun, nsp_typ')) end;
        val add_name =
          case def
           of CodeThingol.Bot => pair base
            | CodeThingol.Fun _ => add_fun false
            | CodeThingol.Datatype _ => add_typ
            | CodeThingol.Datatypecons _ => add_fun true
            | CodeThingol.Class _ => add_typ
            | CodeThingol.Classrel _ => pair base
            | CodeThingol.Classparam _ => add_fun false
            | CodeThingol.Classinst _ => pair base;
        val modlname' = name_modl modl;
        fun add_def base' =
          case def
           of CodeThingol.Bot => I
            | CodeThingol.Datatypecons _ =>
                cons (name, ((NameSpace.append modlname' base', base'), NONE))
            | CodeThingol.Classrel _ => I
            | CodeThingol.Classparam _ =>
                cons (name, ((NameSpace.append modlname' base', base'), NONE))
            | _ => cons (name, ((NameSpace.append modlname' base', base'), SOME def));
      in
        Symtab.map_default (modlname', ([], ([], (init_names, init_names))))
              (apfst (fold (insert (op = : string * string -> bool)) deps))
        #> `(fn code => add_name ((snd o snd o the o Symtab.lookup code) modlname'))
        #-> (fn (base', names) =>
              (Symtab.map_entry modlname' o apsnd) (fn (defs, _) =>
              (add_def base' defs, names)))
      end;
    val code' =
      fold add_def (AList.make (fn name =>
        (Graph.get_node code name, Graph.imm_succs code name))
        (Graph.strong_conn code |> flat)) Symtab.empty;
    val init_syms = CodeName.make_vars reserved_syms;
    fun deresolv name =
      (fst o fst o the o AList.lookup (op =) ((fst o snd o the
        o Symtab.lookup code') ((name_modl o fst o dest_name) name))) name
        handle Option => error ("Unknown definition name: " ^ labelled_name name);
    fun deresolv_here name =
      (snd o fst o the o AList.lookup (op =) ((fst o snd o the
        o Symtab.lookup code') ((name_modl o fst o dest_name) name))) name
        handle Option => error ("Unknown definition name: " ^ labelled_name name);
    fun deriving_show tyco =
      let
        fun deriv _ "fun" = false
          | deriv tycos tyco = member (op =) tycos tyco orelse
              case the_default CodeThingol.Bot (try (Graph.get_node code) tyco)
               of CodeThingol.Bot => true
                | CodeThingol.Datatype (_, cs) => forall (deriv' (tyco :: tycos))
                    (maps snd cs)
        and deriv' tycos (tyco `%% tys) = deriv tycos tyco
              andalso forall (deriv' tycos) tys
          | deriv' _ (ITyVar _) = true
      in deriv [] tyco end;
    fun seri_def qualified = pr_haskell class_syntax tyco_syntax
      const_syntax labelled_name init_syms
      deresolv_here (if qualified then deresolv else deresolv_here) is_cons
      contr_classparam_typs
      (if string_classes then deriving_show else K false);
    fun assemble_module (modulename, content) =
      (modulename, Pretty.chunks [
        str ("module " ^ modulename ^ " where {"),
        str "",
        content,
        str "",
        str "}"
      ]);
    fun seri_module (modlname', (imports, (defs, _))) =
      let
        val imports' =
          imports
          |> map (name_modl o fst o dest_name)
          |> distinct (op =)
          |> remove (op =) modlname';
        val qualified =
          imports @ map fst defs
          |> distinct (op =)
          |> map_filter (try deresolv)
          |> map NameSpace.base
          |> has_duplicates (op =);
        val mk_import = str o (if qualified
          then prefix "import qualified "
          else prefix "import ") o suffix ";";
        fun import_include (name, _) = str ("import " ^ name ^ ";");
        val content = Pretty.chunks (
            map mk_import imports'
            @ map import_include includes
            @ str ""
            :: separate (str "") (map_filter
              (fn (name, (_, SOME def)) => SOME (seri_def qualified (name, def))
                | (_, (_, NONE)) => NONE) defs)
          )
      in assemble_module (modlname', content) end;
    fun write_module destination (modlname, content) =
      let
        val filename = case modlname
         of "" => Path.explode "Main.hs"
          | _ => (Path.ext "hs" o Path.explode o implode o separate "/"
                o NameSpace.explode) modlname;
        val pathname = Path.append destination filename;
        val _ = File.mkdir (Path.dir pathname);
      in File.write pathname (code_source content) end
    val output = case seri_dest
     of Compile => error ("Haskell: no internal compilation")
      | Write => K NONE o map (code_writeln o snd)
      | File destination => K NONE o map (write_module destination)
      | String => SOME o cat_lines o map (code_source o snd);
  in output (map assemble_module includes
    @ map seri_module (Symtab.dest code'))
  end;

fun isar_seri_haskell module =
  parse_args (Scan.option (Args.$$$ "root" -- Args.colon |-- Args.name)
    -- Scan.optional (Args.$$$ "string_classes" >> K true) false
    >> (fn (module_prefix, string_classes) =>
      seri_haskell module_prefix module string_classes));


(** diagnosis serializer **)

fun seri_diagnosis labelled_name _ _ _ _ _ _ code _ _ =
  let
    val init_names = CodeName.make_vars [];
    fun pr_fun "fun" = SOME (2, fn pr_typ => fn fxy => fn [ty1, ty2] =>
          brackify_infix (1, R) fxy [
            pr_typ (INFX (1, X)) ty1,
            str "->",
            pr_typ (INFX (1, R)) ty2
          ])
      | pr_fun _ = NONE
    val pr = pr_haskell (K NONE) pr_fun (K NONE) labelled_name init_names
      I I (K false) (K []) (K false);
  in
    []
    |> Graph.fold (fn (name, (def, _)) =>
          case try pr (name, def) of SOME p => cons p | NONE => I) code
    |> Pretty.chunks2
    |> code_source
    |> writeln
    |> K NONE
  end;


(** optional pretty serialization **)

local

fun ocaml_char c =
  let
    fun chr i =
      let
        val xs = string_of_int i;
        val ys = replicate_string (3 - length (explode xs)) "0";
      in "\\" ^ ys ^ xs end;
    val i = ord c;
    val s = if i < 32 orelse i = 34 orelse i = 39 orelse i = 92 orelse i > 126
      then chr i else c
  in s end;

fun haskell_char c =
  let
    val s = ML_Syntax.print_char c;
  in if s = "'" then "\\'" else s end;

val pretty : (string * {
    pretty_char: string -> string,
    pretty_string: string -> string,
    pretty_numeral: bool -> int -> string,
    pretty_list: Pretty.T list -> Pretty.T,
    infix_cons: int * string
  }) list = [
  ("SML", { pretty_char = prefix "#" o quote o ML_Syntax.print_char,
      pretty_string = quote o translate_string ML_Syntax.print_char,
      pretty_numeral = fn unbounded => fn k =>
        if unbounded then "(" ^ string_of_int k ^ " : IntInf.int)"
        else string_of_int k,
      pretty_list = Pretty.enum "," "[" "]",
      infix_cons = (7, "::")}),
  ("OCaml", { pretty_char = enclose "'" "'" o ocaml_char,
      pretty_string = quote o translate_string ocaml_char,
      pretty_numeral = fn unbounded => fn k => if k >= 0 then
            if unbounded then
              "(Big_int.big_int_of_int " ^ string_of_int k ^ ")"
            else string_of_int k
          else
            if unbounded then
              "(Big_int.big_int_of_int " ^ (enclose "(" ")" o prefix "-"
                o string_of_int o op ~) k ^ ")"
            else (enclose "(" ")" o prefix "-" o string_of_int o op ~) k,
      pretty_list = Pretty.enum ";" "[" "]",
      infix_cons = (6, "::")}),
  ("Haskell", { pretty_char = enclose "'" "'" o haskell_char,
      pretty_string = quote o translate_string haskell_char,
      pretty_numeral = fn unbounded => fn k => if k >= 0 then string_of_int k
          else enclose "(" ")" (signed_string_of_int k),
      pretty_list = Pretty.enum "," "[" "]",
      infix_cons = (5, ":")})
];

in

fun pr_pretty target = case AList.lookup (op =) pretty target
 of SOME x => x
  | NONE => error ("Unknown code target language: " ^ quote target);

fun default_list (target_fxy, target_cons) pr fxy t1 t2 =
  brackify_infix (target_fxy, R) fxy [
    pr (INFX (target_fxy, X)) t1,
    str target_cons,
    pr (INFX (target_fxy, R)) t2
  ];

fun pretty_list c_nil c_cons target =
  let
    val pretty_ops = pr_pretty target;
    val mk_list = #pretty_list pretty_ops;
    fun pretty pr vars fxy [(t1, _), (t2, _)] =
      case Option.map (cons t1) (implode_list c_nil c_cons t2)
       of SOME ts => mk_list (map (pr vars NOBR) ts)
        | NONE => default_list (#infix_cons pretty_ops) (pr vars) fxy t1 t2;
  in (2, pretty) end;

fun pretty_list_string c_nil c_cons c_char c_nibbles target =
  let
    val pretty_ops = pr_pretty target;
    val mk_list = #pretty_list pretty_ops;
    val mk_char = #pretty_char pretty_ops;
    val mk_string = #pretty_string pretty_ops;
    fun pretty pr vars fxy [(t1, _), (t2, _)] =
      case Option.map (cons t1) (implode_list c_nil c_cons t2)
       of SOME ts => (case implode_string c_char c_nibbles mk_char mk_string ts
           of SOME p => p
            | NONE => mk_list (map (pr vars NOBR) ts))
        | NONE => default_list (#infix_cons pretty_ops) (pr vars) fxy t1 t2;
  in (2, pretty) end;

fun pretty_char c_char c_nibbles target =
  let
    val mk_char = #pretty_char (pr_pretty target);
    fun pretty _ _ _ [(t1, _), (t2, _)] =
      case decode_char c_nibbles (t1, t2)
       of SOME c => (str o mk_char) c
        | NONE => error "Illegal character expression";
  in (2, pretty) end;

fun pretty_numeral unbounded negative c_pls c_min c_bit0 c_bit1 target =
  let
    val mk_numeral = #pretty_numeral (pr_pretty target);
    fun pretty _ _ _ [(t, _)] =
      (str o mk_numeral unbounded o implode_numeral negative c_pls c_min c_bit0 c_bit1) t;
  in (1, pretty) end;

fun pretty_message c_char c_nibbles c_nil c_cons target =
  let
    val pretty_ops = pr_pretty target;
    val mk_char = #pretty_char pretty_ops;
    val mk_string = #pretty_string pretty_ops;
    fun pretty pr vars fxy [(t, _)] =
      case implode_list c_nil c_cons t
       of SOME ts => (case implode_string c_char c_nibbles mk_char mk_string ts
           of SOME p => p
            | NONE => error "Illegal message expression")
        | NONE => error "Illegal message expression";
  in (1, pretty) end;

fun pretty_imperative_monad_bind bind' return' unit' =
  let
    val dummy_name = "";
    val dummy_type = ITyVar dummy_name;
    val dummy_case_term = IVar dummy_name;
    (*assumption: dummy values are not relevant for serialization*)
    val unitt = IConst (unit', ([], []));
    fun dest_abs ((v, ty) `|-> t, _) = ((v, ty), t)
      | dest_abs (t, ty) =
          let
            val vs = CodeThingol.fold_varnames cons t [];
            val v = Name.variant vs "x";
            val ty' = (hd o fst o CodeThingol.unfold_fun) ty;
          in ((v, ty'), t `$ IVar v) end;
    fun force (t as IConst (c, _) `$ t') = if c = return'
          then t' else t `$ unitt
      | force t = t `$ unitt;
    fun tr_bind' [(t1, _), (t2, ty2)] =
      let
        val ((v, ty), t) = dest_abs (t2, ty2);
      in ICase (((force t1, ty), [(IVar v, tr_bind'' t)]), dummy_case_term) end
    and tr_bind'' t = case CodeThingol.unfold_app t
         of (IConst (c, (_, ty1 :: ty2 :: _)), [x1, x2]) => if c = bind'
              then tr_bind' [(x1, ty1), (x2, ty2)]
              else force t
          | _ => force t;
    fun tr_bind ts = (dummy_name, dummy_type)
      `|-> ICase (((IVar dummy_name, dummy_type), [(unitt, tr_bind' ts)]), dummy_case_term);
    fun pretty pr vars fxy ts = pr vars fxy (tr_bind ts);
  in (2, pretty) end;

fun no_bindings x = (Option.map o apsnd)
  (fn pretty => fn pr => fn vars => pretty (pr vars)) x;

end; (*local*)


(** user interfaces **)

(* evaluation *)

fun eval_seri module args =
  seri_ml (use_text (1, "generated code") Output.ml_output false)
    (fn (cs, SOME s) => "let\n" ^ s ^ "\nin fn () => " ^ enclose "(" ")" (commas cs) ^ " end")
    pr_sml (K Pretty.chunks) (SOME "Isabelle_Eval");

fun sml_of thy code cs = get_serializer (K eval_seri) thy target_SML false NONE [] code (SOME cs) String;

fun eval thy (ref_name, reff) code (t, ty) args =
  let
    val _ = if CodeThingol.contains_dictvar t then
      error "Term to be evaluated constains free dictionaries" else ();
    val code' = CodeThingol.add_value_stmt (t, ty) code;
    val value_code = sml_of thy code' [CodeName.value_name] ;
    val sml_code = space_implode " " (value_code :: "()" :: map (enclose "(" ")") args);
  in ML_Context.evaluate Output.ml_output false (ref_name, reff) sml_code end;


(* infix syntax *)

datatype 'a mixfix =
    Arg of fixity
  | Pretty of Pretty.T;

fun mk_mixfix prep_arg (fixity_this, mfx) =
  let
    fun is_arg (Arg _) = true
      | is_arg _ = false;
    val i = (length o filter is_arg) mfx;
    fun fillin _ [] [] =
          []
      | fillin pr (Arg fxy :: mfx) (a :: args) =
          (pr fxy o prep_arg) a :: fillin pr mfx args
      | fillin pr (Pretty p :: mfx) args =
          p :: fillin pr mfx args
      | fillin _ [] _ =
          error ("Inconsistent mixfix: too many arguments")
      | fillin _ _ [] =
          error ("Inconsistent mixfix: too less arguments");
  in
    (i, fn pr => fn fixity_ctxt => fn args =>
      gen_brackify (fixity fixity_this fixity_ctxt) (fillin pr mfx args))
  end;

fun parse_infix prep_arg (x, i) s =
  let
    val l = case x of L => INFX (i, L) | _ => INFX (i, X);
    val r = case x of R => INFX (i, R) | _ => INFX (i, X);
  in
    mk_mixfix prep_arg (INFX (i, x),
      [Arg l, (Pretty o Pretty.brk) 1, (Pretty o str) s, (Pretty o Pretty.brk) 1, Arg r])
  end;


(* data access *)

local

fun cert_class thy class =
  let
    val _ = AxClass.get_info thy class;
  in class end;

fun read_class thy raw_class =
  let
    val class = Sign.intern_class thy raw_class;
    val _ = AxClass.get_info thy class;
  in class end;

fun cert_tyco thy tyco =
  let
    val _ = if Sign.declared_tyname thy tyco then ()
      else error ("No such type constructor: " ^ quote tyco);
  in tyco end;

fun read_tyco thy raw_tyco =
  let
    val tyco = Sign.intern_type thy raw_tyco;
    val _ = if Sign.declared_tyname thy tyco then ()
      else error ("No such type constructor: " ^ quote raw_tyco);
  in tyco end;

fun gen_add_syntax_class prep_class prep_const target raw_class raw_syn thy =
  let
    val class = prep_class thy raw_class;
    val class' = CodeName.class thy class;
    fun mk_classparam c = case AxClass.class_of_param thy c
     of SOME class'' => if class = class'' then CodeName.const thy c
          else error ("Not a class operation for class " ^ quote class ^ ": " ^ quote c)
      | NONE => error ("Not a class operation: " ^ quote c);
    fun mk_syntax_params raw_params = AList.lookup (op =)
      ((map o apfst) (mk_classparam o prep_const thy) raw_params);
  in case raw_syn
   of SOME (syntax, raw_params) =>
      thy
      |> (map_syntax_exprs target o apfst o apfst)
           (Symtab.update (class', (syntax, mk_syntax_params raw_params)))
    | NONE =>
      thy
      |> (map_syntax_exprs target o apfst o apfst)
           (Symtab.delete_safe class')
  end;

fun gen_add_syntax_inst prep_class prep_tyco target (raw_tyco, raw_class) add_del thy =
  let
    val inst = CodeName.instance thy (prep_class thy raw_class, prep_tyco thy raw_tyco);
  in if add_del then
    thy
    |> (map_syntax_exprs target o apfst o apsnd)
        (Symtab.update (inst, ()))
  else
    thy
    |> (map_syntax_exprs target o apfst o apsnd)
        (Symtab.delete_safe inst)
  end;

fun gen_add_syntax_tyco prep_tyco target raw_tyco raw_syn thy =
  let
    val tyco = prep_tyco thy raw_tyco;
    val tyco' = if tyco = "fun" then "fun" else CodeName.tyco thy tyco;
    fun check_args (syntax as (n, _)) = if n <> Sign.arity_number thy tyco
      then error ("Number of arguments mismatch in syntax for type constructor " ^ quote tyco)
      else syntax
  in case raw_syn
   of SOME syntax =>
      thy
      |> (map_syntax_exprs target o apsnd o apfst)
           (Symtab.update (tyco', check_args syntax))
   | NONE =>
      thy
      |> (map_syntax_exprs target o apsnd o apfst)
           (Symtab.delete_safe tyco')
  end;

fun gen_add_syntax_const prep_const target raw_c raw_syn thy =
  let
    val c = prep_const thy raw_c;
    val c' = CodeName.const thy c;
    fun check_args (syntax as (n, _)) = if n > CodeUnit.no_args thy c
      then error ("Too many arguments in syntax for constant " ^ quote c)
      else syntax;
  in case raw_syn
   of SOME syntax =>
      thy
      |> (map_syntax_exprs target o apsnd o apsnd)
           (Symtab.update (c', check_args syntax))
   | NONE =>
      thy
      |> (map_syntax_exprs target o apsnd o apsnd)
           (Symtab.delete_safe c')
  end;

fun add_reserved target =
  let
    fun add sym syms = if member (op =) syms sym
      then error ("Reserved symbol " ^ quote sym ^ " already declared")
      else insert (op =) sym syms
  in map_adaptions target o apfst o add end;

fun add_include target =
  let
    fun add (name, SOME content) incls =
          let
            val _ = if Symtab.defined incls name
              then warning ("Overwriting existing include " ^ name)
              else ();
          in Symtab.update (name, str content) incls end
      | add (name, NONE) incls =
          Symtab.delete name incls;
  in map_adaptions target o apsnd o add end;

fun add_modl_alias target =
  map_module_alias target o Symtab.update o apsnd CodeName.check_modulename;

fun add_monad target c_run c_bind c_return_unit thy =
  let
    val c_run' = CodeUnit.read_const thy c_run;
    val c_bind' = CodeUnit.read_const thy c_bind;
    val c_bind'' = CodeName.const thy c_bind';
    val c_return_unit'' = (Option.map o pairself)
      (CodeName.const thy o CodeUnit.read_const thy) c_return_unit;
    val is_haskell = target = target_Haskell;
    val _ = if is_haskell andalso is_some c_return_unit''
      then error ("No unit entry may be given for Haskell monad")
      else ();
    val _ = if not is_haskell andalso is_none c_return_unit''
      then error ("Unit entry must be given for SML/OCaml monad")
      else ();
  in if target = target_Haskell then
    thy
    |> gen_add_syntax_const (K I) target_Haskell c_run'
          (SOME (pretty_haskell_monad c_bind''))
    |> gen_add_syntax_const (K I) target_Haskell c_bind'
          (no_bindings (SOME (parse_infix fst (L, 1) ">>=")))
  else
    thy
    |> gen_add_syntax_const (K I) target c_bind'
          (SOME (pretty_imperative_monad_bind c_bind''
            ((fst o the) c_return_unit'') ((snd o the) c_return_unit'')))
  end;

fun gen_allow_exception prep_cs raw_c thy =
  let
    val c = prep_cs thy raw_c;
    val c' = CodeName.const thy c;
  in thy |> (CodeTargetData.map o apsnd) (insert (op =) c') end;

fun zip_list (x::xs) f g =
  f
  #-> (fn y =>
    fold_map (fn x => g |-- f >> pair x) xs
    #-> (fn xys => pair ((x, y) :: xys)));


(* conrete syntax *)

structure P = OuterParse
and K = OuterKeyword

fun parse_multi_syntax parse_thing parse_syntax =
  P.and_list1 parse_thing
  #-> (fn things => Scan.repeat1 (P.$$$ "(" |-- P.name --
        (zip_list things parse_syntax (P.$$$ "and")) --| P.$$$ ")"));

val (infixK, infixlK, infixrK) = ("infix", "infixl", "infixr");

fun parse_mixfix prep_arg s =
  let
    val sym_any = Scan.one Symbol.is_regular;
    val parse = Scan.optional ($$ "!" >> K true) false -- Scan.repeat (
         ($$ "(" -- $$ "_" -- $$ ")" >> K (Arg NOBR))
      || ($$ "_" >> K (Arg BR))
      || ($$ "/" |-- Scan.repeat ($$ " ") >> (Pretty o Pretty.brk o length))
      || (Scan.repeat1
           (   $$ "'" |-- sym_any
            || Scan.unless ($$ "_" || $$ "/" || $$ "(" |-- $$ "_" |-- $$ ")")
                 sym_any) >> (Pretty o str o implode)));
  in case Scan.finite Symbol.stopper parse (Symbol.explode s)
   of ((_, p as [_]), []) => mk_mixfix prep_arg (NOBR, p)
    | ((b, p as _ :: _ :: _), []) => mk_mixfix prep_arg (if b then NOBR else BR, p)
    | _ => Scan.!!
        (the_default ("malformed mixfix annotation: " ^ quote s) o snd) Scan.fail ()
  end;

fun parse_syntax prep_arg xs =
  Scan.option ((
      ((P.$$$ infixK  >> K X)
        || (P.$$$ infixlK >> K L)
        || (P.$$$ infixrK >> K R))
        -- P.nat >> parse_infix prep_arg
      || Scan.succeed (parse_mixfix prep_arg))
      -- P.string
      >> (fn (parse, s) => parse s)) xs;

in

val parse_syntax = parse_syntax;

val add_syntax_class = gen_add_syntax_class cert_class (K I);
val add_syntax_inst = gen_add_syntax_inst cert_class cert_tyco;
val add_syntax_tyco = gen_add_syntax_tyco cert_tyco;
val add_syntax_const = gen_add_syntax_const (K I);
val allow_exception = gen_allow_exception (K I);

val add_syntax_class_cmd = gen_add_syntax_class read_class CodeUnit.read_const;
val add_syntax_inst_cmd = gen_add_syntax_inst read_class read_tyco;
val add_syntax_tyco_cmd = gen_add_syntax_tyco read_tyco;
val add_syntax_const_cmd = gen_add_syntax_const CodeUnit.read_const;
val allow_exception_cmd = gen_allow_exception CodeUnit.read_const;

fun add_syntax_tycoP target tyco = parse_syntax I >> add_syntax_tyco_cmd target tyco;
fun add_syntax_constP target c = parse_syntax fst >> (add_syntax_const_cmd target c o no_bindings);

fun add_undefined target undef target_undefined thy =
  let
    fun pr _ _ _ _ = str target_undefined;
  in
    thy
    |> add_syntax_const target undef (SOME (~1, pr))
  end;

fun add_pretty_list target nill cons thy =
  let
    val nil' = CodeName.const thy nill;
    val cons' = CodeName.const thy cons;
    val pr = pretty_list nil' cons' target;
  in
    thy
    |> add_syntax_const target cons (SOME pr)
  end;

fun add_pretty_list_string target nill cons charr nibbles thy =
  let
    val nil' = CodeName.const thy nill;
    val cons' = CodeName.const thy cons;
    val charr' = CodeName.const thy charr;
    val nibbles' = map (CodeName.const thy) nibbles;
    val pr = pretty_list_string nil' cons' charr' nibbles' target;
  in
    thy
    |> add_syntax_const target cons (SOME pr)
  end;

fun add_pretty_char target charr nibbles thy =
  let
    val charr' = CodeName.const thy charr;
    val nibbles' = map (CodeName.const thy) nibbles;
    val pr = pretty_char charr' nibbles' target;
  in
    thy
    |> add_syntax_const target charr (SOME pr)
  end;

fun add_pretty_numeral target unbounded negative number_of pls min bit0 bit1 thy =
  let
    val pls' = CodeName.const thy pls;
    val min' = CodeName.const thy min;
    val bit0' = CodeName.const thy bit0;
    val bit1' = CodeName.const thy bit1;
    val pr = pretty_numeral unbounded negative pls' min' bit0' bit1' target;
  in
    thy
    |> add_syntax_const target number_of (SOME pr)
  end;

fun add_pretty_message target charr nibbles nill cons str thy =
  let
    val charr' = CodeName.const thy charr;
    val nibbles' = map (CodeName.const thy) nibbles;
    val nil' = CodeName.const thy nill;
    val cons' = CodeName.const thy cons;
    val pr = pretty_message charr' nibbles' nil' cons' target;
  in
    thy
    |> add_syntax_const target str (SOME pr)
  end;


(* Isar commands *)

val _ = OuterSyntax.keywords [infixK, infixlK, infixrK];

val _ =
  OuterSyntax.command "code_class" "define code syntax for class" K.thy_decl (
    parse_multi_syntax P.xname
      (Scan.option (P.string -- Scan.optional (P.$$$ "where" |-- Scan.repeat1
        (P.term --| (P.$$$ "\<equiv>" || P.$$$ "==") -- P.string)) []))
    >> (Toplevel.theory oo fold) (fn (target, syns) =>
          fold (fn (raw_class, syn) => add_syntax_class_cmd target raw_class syn) syns)
  );

val _ =
  OuterSyntax.command "code_instance" "define code syntax for instance" K.thy_decl (
    parse_multi_syntax (P.xname --| P.$$$ "::" -- P.xname)
      ((P.minus >> K true) || Scan.succeed false)
    >> (Toplevel.theory oo fold) (fn (target, syns) =>
          fold (fn (raw_inst, add_del) => add_syntax_inst_cmd target raw_inst add_del) syns)
  );

val _ =
  OuterSyntax.command "code_type" "define code syntax for type constructor" K.thy_decl (
    parse_multi_syntax P.xname (parse_syntax I)
    >> (Toplevel.theory oo fold) (fn (target, syns) =>
          fold (fn (raw_tyco, syn) => add_syntax_tyco_cmd target raw_tyco syn) syns)
  );

val _ =
  OuterSyntax.command "code_const" "define code syntax for constant" K.thy_decl (
    parse_multi_syntax P.term (parse_syntax fst)
    >> (Toplevel.theory oo fold) (fn (target, syns) =>
          fold (fn (raw_const, syn) => add_syntax_const_cmd target raw_const (no_bindings syn)) syns)
  );

val _ =
  OuterSyntax.command "code_monad" "define code syntax for monads" K.thy_decl (
    P.term -- P.term -- ((P.term -- P.term >> SOME) -- Scan.repeat1 P.name
      || Scan.succeed NONE -- Scan.repeat1 P.name)
    >> (fn ((raw_run, raw_bind), (raw_unit_return, targets)) => Toplevel.theory 
          (fold (fn target => add_monad target raw_run raw_bind raw_unit_return) targets))
  );

val _ =
  OuterSyntax.command "code_reserved" "declare words as reserved for target language" K.thy_decl (
    P.name -- Scan.repeat1 P.name
    >> (fn (target, reserveds) => (Toplevel.theory o fold (add_reserved target)) reserveds)
  );

val _ =
  OuterSyntax.command "code_include" "declare piece of code to be included in generated code" K.thy_decl (
    P.name -- P.name -- (P.text >> (fn "-" => NONE | s => SOME s))
    >> (fn ((target, name), content) => (Toplevel.theory o add_include target)
      (name, content))
  );

val _ =
  OuterSyntax.command "code_modulename" "alias module to other name" K.thy_decl (
    P.name -- Scan.repeat1 (P.name -- P.name)
    >> (fn (target, modlnames) => (Toplevel.theory o fold (add_modl_alias target)) modlnames)
  );

val _ =
  OuterSyntax.command "code_exception" "permit exceptions for constant" K.thy_decl (
    Scan.repeat1 P.term >> (Toplevel.theory o fold allow_exception_cmd)
  );


(* serializer setup, including serializer defaults *)

val setup =
  add_serializer (target_SML, isar_seri_sml)
  #> add_serializer (target_OCaml, isar_seri_ocaml)
  #> add_serializer (target_Haskell, isar_seri_haskell)
  #> add_serializer (target_diag, fn _ => fn _=> seri_diagnosis)
  #> add_syntax_tyco "SML" "fun" (SOME (2, fn pr_typ => fn fxy => fn [ty1, ty2] =>
      (gen_brackify (case fxy of NOBR => false | _ => fixity (INFX (1, R)) fxy) o Pretty.breaks) [
        pr_typ (INFX (1, X)) ty1,
        str "->",
        pr_typ (INFX (1, R)) ty2
      ]))
  #> add_syntax_tyco "OCaml" "fun" (SOME (2, fn pr_typ => fn fxy => fn [ty1, ty2] =>
      (gen_brackify (case fxy of NOBR => false | _ => fixity (INFX (1, R)) fxy) o Pretty.breaks) [
        pr_typ (INFX (1, X)) ty1,
        str "->",
        pr_typ (INFX (1, R)) ty2
      ]))
  #> add_syntax_tyco "Haskell" "fun" (SOME (2, fn pr_typ => fn fxy => fn [ty1, ty2] =>
      brackify_infix (1, R) fxy [
        pr_typ (INFX (1, X)) ty1,
        str "->",
        pr_typ (INFX (1, R)) ty2
      ]))
  #> fold (add_reserved "SML") ML_Syntax.reserved_names
  #> fold (add_reserved "SML")
      ["o" (*dictionary projections use it already*), "Fail", "div", "mod" (*standard infixes*)]
  #> fold (add_reserved "OCaml") [
      "and", "as", "assert", "begin", "class",
      "constraint", "do", "done", "downto", "else", "end", "exception",
      "external", "false", "for", "fun", "function", "functor", "if",
      "in", "include", "inherit", "initializer", "lazy", "let", "match", "method",
      "module", "mutable", "new", "object", "of", "open", "or", "private", "rec",
      "sig", "struct", "then", "to", "true", "try", "type", "val",
      "virtual", "when", "while", "with"
    ]
  #> fold (add_reserved "OCaml") ["failwith", "mod"]
  #> fold (add_reserved "Haskell") [
      "hiding", "deriving", "where", "case", "of", "infix", "infixl", "infixr",
      "import", "default", "forall", "let", "in", "class", "qualified", "data",
      "newtype", "instance", "if", "then", "else", "type", "as", "do", "module"
    ]
  #> fold (add_reserved "Haskell") [
      "Prelude", "Main", "Bool", "Maybe", "Either", "Ordering", "Char", "String", "Int",
      "Integer", "Float", "Double", "Rational", "IO", "Eq", "Ord", "Enum", "Bounded",
      "Num", "Real", "Integral", "Fractional", "Floating", "RealFloat", "Monad", "Functor",
      "AlreadyExists", "ArithException", "ArrayException", "AssertionFailed", "AsyncException",
      "BlockedOnDeadMVar", "Deadlock", "Denormal", "DivideByZero", "DotNetException", "DynException",
      "Dynamic", "EOF", "EQ", "EmptyRec", "ErrorCall", "ExitException", "ExitFailure",
      "ExitSuccess", "False", "GT", "HeapOverflow",
      "IOError", "IOException", "IllegalOperation",
      "IndexOutOfBounds", "Just", "Key", "LT", "Left", "LossOfPrecision", "NoMethodError",
      "NoSuchThing", "NonTermination", "Nothing", "Obj", "OtherError", "Overflow",
      "PatternMatchFail", "PermissionDenied", "ProtocolError", "RecConError", "RecSelError",
      "RecUpdError", "ResourceBusy", "ResourceExhausted", "Right", "StackOverflow",
      "ThreadKilled", "True", "TyCon", "TypeRep", "UndefinedElement", "Underflow",
      "UnsupportedOperation", "UserError", "abs", "absReal", "acos", "acosh", "all",
      "and", "any", "appendFile", "asTypeOf", "asciiTab", "asin", "asinh", "atan",
      "atan2", "atanh", "basicIORun", "blockIO", "boundedEnumFrom", "boundedEnumFromThen",
      "boundedEnumFromThenTo", "boundedEnumFromTo", "boundedPred", "boundedSucc", "break",
      "catch", "catchException", "ceiling", "compare", "concat", "concatMap", "const",
      "cos", "cosh", "curry", "cycle", "decodeFloat", "denominator", "div", "divMod",
      "doubleToRatio", "doubleToRational", "drop", "dropWhile", "either", "elem",
      "emptyRec", "encodeFloat", "enumFrom", "enumFromThen", "enumFromThenTo",
      "enumFromTo", "error", "even", "exp", "exponent", "fail", "filter", "flip",
      "floatDigits", "floatProperFraction", "floatRadix", "floatRange", "floatToRational",
      "floor", "fmap", "foldl", "foldl'", "foldl1", "foldr", "foldr1", "fromDouble",
      "fromEnum", "fromEnum_0", "fromInt", "fromInteger", "fromIntegral", "fromObj",
      "fromRational", "fst", "gcd", "getChar", "getContents", "getLine", "head",
      "id", "inRange", "index", "init", "intToRatio", "interact", "ioError", "isAlpha",
      "isAlphaNum", "isDenormalized", "isDigit", "isHexDigit", "isIEEE", "isInfinite",
      "isLower", "isNaN", "isNegativeZero", "isOctDigit", "isSpace", "isUpper", "iterate", "iterate'",
      "last", "lcm", "length", "lex", "lexDigits", "lexLitChar", "lexmatch", "lines", "log",
      "logBase", "lookup", "loop", "map", "mapM", "mapM_", "max", "maxBound", "maximum",
      "maybe", "min", "minBound", "minimum", "mod", "negate", "nonnull", "not", "notElem",
      "null", "numerator", "numericEnumFrom", "numericEnumFromThen", "numericEnumFromThenTo",
      "numericEnumFromTo", "odd", "or", "otherwise", "pi", "pred", 
      "print", "product", "properFraction", "protectEsc", "putChar", "putStr", "putStrLn",
      "quot", "quotRem", "range", "rangeSize", "rationalToDouble", "rationalToFloat",
      "rationalToRealFloat", "read", "readDec", "readField", "readFieldName", "readFile",
      "readFloat", "readHex", "readIO", "readInt", "readList", "readLitChar", "readLn",
      "readOct", "readParen", "readSigned", "reads", "readsPrec", "realFloatToRational",
      "realToFrac", "recip", "reduce", "rem", "repeat", "replicate", "return", "reverse",
      "round", "scaleFloat", "scanl", "scanl1", "scanr", "scanr1", "seq", "sequence",
      "sequence_", "show", "showChar", "showException", "showField", "showList",
      "showLitChar", "showParen", "showString", "shows", "showsPrec", "significand",
      "signum", "signumReal", "sin", "sinh", "snd", "span", "splitAt", "sqrt", "subtract",
      "succ", "sum", "tail", "take", "takeWhile", "takeWhile1", "tan", "tanh", "threadToIOResult",
      "throw", "toEnum", "toInt", "toInteger", "toObj", "toRational", "truncate", "uncurry",
      "undefined", "unlines", "unsafeCoerce", "unsafeIndex", "unsafeRangeSize", "until", "unwords",
      "unzip", "unzip3", "userError", "words", "writeFile", "zip", "zip3", "zipWith", "zipWith3"
    ] (*due to weird handling of ':', we can't do anything else than to import *all* prelude symbols*);

end; (*local*)

end; (*struct*)
