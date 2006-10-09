(*  Title:      Pure/Tools/codegen_serializer.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Serializer from intermediate language ("Thin-gol") to
target languages (like SML or Haskell).
*)

signature CODEGEN_SERIALIZER =
sig
  include BASIC_CODEGEN_THINGOL;
  val get_serializer: theory -> string * Args.T list
    -> string list option -> CodegenThingol.code -> unit;
  val eval_verbose: bool ref;
  val eval_term: theory ->
    (string * 'a option ref) * CodegenThingol.iterm -> CodegenThingol.code
    -> 'a;
  val const_has_serialization: theory -> string list -> string -> bool;
  val tyco_has_serialization: theory -> string list -> string -> bool;
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

  type fixity;
  type serializer;
  val add_serializer : string * serializer -> theory -> theory;
  val ml_from_thingol: serializer;
  val hs_from_thingol: serializer;
end;

structure CodegenSerializer: CODEGEN_SERIALIZER =
struct

open BasicCodegenThingol;
val tracing = CodegenThingol.tracing;

(** syntax **)

(* basics *)

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

fun mk_app mk_app' from_expr const_syntax fxy (const as (c, (_, ty)), es) =
  case const_syntax c
   of NONE => brackify fxy (mk_app' c es)
    | SOME (i, pr) =>
        let
          val k = if i < 0 then (length o fst o CodegenThingol.unfold_fun) ty else i
        in if k <= length es
          then case chop i es of (es1, es2) =>
            brackify fxy (pr fxy from_expr es1 :: map (from_expr BR) es2)
          else from_expr fxy (CodegenThingol.eta_expand (const, es) i)
        end;

val first_upper = implode o nth_map 0 Symbol.to_ascii_upper o explode;


(* user-defined syntax *)

val str = setmp print_mode [] Pretty.str;

val (atomK, infixK, infixlK, infixrK) =
  ("target_atom", "infix", "infixl", "infixr");
val _ = OuterSyntax.add_keywords [atomK, infixK, infixlK, infixrK];

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


(* list and string serializer *)

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


(* variable name contexts *)

(*FIXME could name.ML do th whole job?*)
fun make_vars names = (fold (fn name => Symtab.update_new (name, name)) names Symtab.empty,
  Name.make_context names);

fun intro_vars names (namemap, namectxt) =
  let
    val (names', namectxt') = Name.variants names namectxt;
    val namemap' = fold2 (curry Symtab.update) names names' namemap;
  in (namemap', namectxt') end;

fun lookup_var (namemap, _) name = case Symtab.lookup namemap name
 of SOME name' => name'
  | NONE => error ("invalid name in context: " ^ quote name);

fun constructive_fun (name, (eqs, ty)) =
  let
    val is_cons = CodegenNames.has_nsp CodegenNames.nsp_dtco;
    fun is_pat (IConst (c, _)) = is_cons c
      | is_pat (IVar _) = true
      | is_pat (t1 `$ t2) =
          is_pat t1 andalso is_pat t2
      | is_pat (INum _) = true
      | is_pat (IChar _) = true
      | is_pat _ = false;
    fun check_eq (eq as (lhs, rhs)) =
      if forall is_pat lhs
      then SOME eq
      else (warning ("In function " ^ quote name ^ ", throwing away one "
        ^ "non-executable function clause"); NONE)
  in case map_filter check_eq eqs
   of [] => error ("In function " ^ quote name ^ ", no "
        ^ "executable function clauses found")
    | eqs => (name, (eqs, ty))
  end;


(** SML serializer **)

datatype ml_def =
    MLFuns of (string * ((iterm list * iterm) list * typscheme)) list
  | MLDatas of (string * ((vname * sort) list * (string * itype list) list)) list
  | MLClass of string * (class list * (vname * (string * itype) list))
  | MLClassinst of string * ((class * (string * (vname * sort) list))
        * ((class * (string * inst list list)) list
      * (string * iterm) list));

fun pr_sml_def tyco_syntax const_syntax keyword_vars deresolv ml_def =
  let
    val is_cons = CodegenNames.has_nsp CodegenNames.nsp_dtco;
    fun dictvar v = 
      first_upper v ^ "_";
    val label = translate_string (fn "." => "__" | c => c)
      o NameSpace.pack o op @ o apsnd single o apfst (fst o split_last) o split_last o NameSpace.unpack;
    fun pr_tyvar (v, []) =
          str "()"
      | pr_tyvar (v, sort) =
          let
            fun pr_class class =
              str ("'" ^ v ^ " " ^ deresolv class);
          in
            Pretty.block [
              str "(",
              (str o dictvar) v,
              str ":",
              case sort
               of [class] => pr_class class
                | _ => Pretty.enum " *" "" "" (map pr_class sort),
              str ")"
            ]
          end;
    fun pr_insts fxy iys =
      let
        fun pr_proj s = str ("#" ^ s);
        fun pr_lookup [] p =
              p
          | pr_lookup [p'] p =
              brackify BR [p', p]
          | pr_lookup (ps as _ :: _) p =
              brackify BR [Pretty.enum " o" "(" ")" ps, p];
        fun pr_inst fxy (Instance (inst, iss)) =
              brackify fxy (
                (str o deresolv) inst
                :: map (pr_insts BR) iss
              )
          | pr_inst fxy (Context (classes, (v, i))) =
              pr_lookup (map (pr_proj o label) classes
                @ (if i = ~1 then [] else [(pr_proj o string_of_int) (i+1)])
              ) ((str o dictvar) v);
      in case iys
       of [] => str "()"
        | [iy] => pr_inst fxy iy
        | _ :: _ => (Pretty.list "(" ")" o map (pr_inst NOBR)) iys
      end;
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
                else pr fxy pr_typ tys)
      | pr_typ fxy (t1 `-> t2) =
          (gen_brackify (case fxy of BR => false | _ => eval_fxy (INFX (1, R)) fxy)
            o Pretty.breaks) [
              pr_typ (INFX (1, X)) t1,
              str "->",
              pr_typ (INFX (1, R)) t2
            ]
      | pr_typ fxy (ITyVar v) =
          str ("'" ^ v);
    fun pr_term vars fxy (IConst c) =
          pr_app vars fxy (c, [])
      | pr_term vars fxy (IVar v) =
          str (lookup_var vars v)
      | pr_term vars fxy (t as t1 `$ t2) =
          (case CodegenThingol.unfold_const_app t
           of SOME c_ts => pr_app vars fxy c_ts
            | NONE =>
                brackify fxy [pr_term vars NOBR t1, pr_term vars BR t2 ])
      | pr_term vars fxy (t as _ `|-> _) =
          let
            val (ts, t') = CodegenThingol.unfold_abs t;
            val vs = fold (CodegenThingol.fold_varnames (insert (op =)) o fst) ts [];
            val vars' = intro_vars vs vars;
            fun mk_abs (t, ty) = (Pretty.block o Pretty.breaks)
              [str "fn", pr_term vars' NOBR t, str "=>"];
          in brackify BR (map mk_abs ts @ [pr_term vars' NOBR t']) end
      | pr_term vars fxy (INum (n, _)) =
          brackify BR [(str o IntInf.toString) n, str ":", str "IntInf.int"]
      | pr_term vars _ (IChar (c, _)) =
          (str o prefix "#" o quote)
            (let val i = ord c
              in if i < 32
                then prefix "\\" (string_of_int i)
                else c
              end)
      | pr_term vars fxy (t as ICase ((_, [_]), _)) =
          let
            val (ts, t) = CodegenThingol.unfold_let t;
            fun mk ((p, _), t) vars =
              let
                val vs = CodegenThingol.fold_varnames (insert (op =)) p [];
                val vars' = intro_vars vs vars;
              in
                (Pretty.block [
                  (Pretty.block o Pretty.breaks) [
                    str "val",
                    pr_term vars' NOBR p,
                    str "=",
                    pr_term vars NOBR t
                  ],
                  str ";"
                ], vars')
              end
            val (binds, vars') = fold_map mk ts vars;
          in
            Pretty.chunks [
              [str ("let"), Pretty.fbrk, binds |> Pretty.chunks] |> Pretty.block,
              [str ("in"), Pretty.fbrk, pr_term vars' NOBR t] |> Pretty.block,
              str ("end")
            ] end
      | pr_term vars fxy (ICase (((td, ty), b::bs), _)) =
          let
            fun pr definer (p, t) =
              let
                val vs = CodegenThingol.fold_varnames (insert (op =)) p [];
                val vars' = intro_vars vs vars;
              in
                (Pretty.block o Pretty.breaks) [
                  str definer,
                  pr_term vars' NOBR p,
                  str "=>",
                  pr_term vars' NOBR t
                ]
              end;
          in
            (Pretty.enclose "(" ")" o single o brackify fxy) (
              str "case"
              :: pr_term vars NOBR td
              :: pr "of" b
              :: map (pr "|") bs
            )
          end
    and pr_app' vars c ts =
      let
        val p = (str o deresolv) c;
        val ps = map (pr_term vars BR) ts;
      in if is_cons c andalso length ts > 1 then
        [p, Pretty.enum "," "(" ")" ps]
      else
        p :: ps
      end
    and pr_app vars fxy (app as ((c, (iss, ty)), ts)) =
      case if is_cons c then [] else (map (pr_insts BR) o filter_out null) iss
       of [] =>
            mk_app (pr_app' vars) (pr_term vars) const_syntax fxy app
        | ps =>
            if (is_none o const_syntax) c then
              brackify fxy ((str o deresolv) c :: (ps @ map (pr_term vars BR) ts))
            else
              error ("Cannot apply user defined serialization for function expecting dictionaries: " ^ quote c)
    fun eta_expand_poly_fun (funn as (_, (_::_, _))) =
          funn
      | eta_expand_poly_fun (funn as (_, ([_], ([], _)))) =
          funn
      | eta_expand_poly_fun (funn as (_, ([(_::_, _)], _))) =
          funn
      | eta_expand_poly_fun (funn as (_, ([(_, _ `|-> _)], _))) =
          funn
      | eta_expand_poly_fun (funn as (name, ([([], t)], tysm as (vs, ty)))) =
          if (null o fst o CodegenThingol.unfold_fun) ty
              orelse (not o null o filter_out (null o snd)) vs
            then funn
            else (name, ([([IVar "x"], t `$ IVar "x")], tysm));
    fun pr_def (MLFuns raw_funns) =
          let
            val funns as (funn :: funns') = map (eta_expand_poly_fun o constructive_fun) raw_funns;
            val definer =
              let
                fun mk [] [] = "val"
                  | mk (_::_) _ = "fun"
                  | mk [] vs = if (null o filter_out (null o snd)) vs then "val" else "fun";
                fun chk (_, ((ts, _) :: _, (vs, _))) NONE = SOME (mk ts vs)
                  | chk (_, ((ts, _) :: _, (vs, _))) (SOME defi) =
                      if defi = mk ts vs then SOME defi
                      else error ("Mixing simultaneous vals and funs not implemented");
              in the (fold chk funns NONE) end;
            fun pr_funn definer (name, (eqs as eq::eqs', (raw_vs, ty))) =
              let
                val vs = filter_out (null o snd) raw_vs;
                val shift = if null eqs' then I else
                  map (Pretty.block o single o Pretty.block o single);
                fun pr_eq definer (ts, t) =
                  let
                    val consts = map_filter
                      (fn c => if (is_some o const_syntax) c
                        then NONE else (SOME o NameSpace.base o deresolv) c)
                        ((fold o CodegenThingol.fold_constnames) (insert (op =)) (t :: ts) []);
                    val vars = keyword_vars
                      |> intro_vars consts
                      |> intro_vars ((fold o CodegenThingol.fold_unbound_varnames) (insert (op =)) (t :: ts) []);
                  in
                    (Pretty.block o Pretty.breaks) (
                      [str definer, (str o deresolv) name]
                      @ (if null ts andalso null vs
                           andalso not (ty = ITyVar "_")(*for evaluation*)
                         then [str ":", pr_typ NOBR ty]
                         else
                           map pr_tyvar vs
                           @ map (pr_term vars BR) ts)
                   @ [str "=", pr_term vars NOBR t]
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
                  (Pretty.block o Pretty.breaks) [
                    str (deresolv co),
                    str "of",
                    Pretty.enum " *" "" "" (map (pr_typ (INFX (2, L))) tys)
                  ];
            fun pr_data definer (tyco, (vs, cos)) =
              (Pretty.block o Pretty.breaks) (
                str definer
                :: pr_tycoexpr NOBR (tyco, map (ITyVar o fst) vs)
                :: str "="
                :: separate (str "|") (map pr_co cos)
              );
            val (ps, p) = split_last (pr_data "datatype" data :: map (pr_data "and") datas');
          in Pretty.chunks (ps @ [Pretty.block ([p, str ";"])]) end
     | pr_def (MLClass (class, (superclasses, (v, classops)))) =
          let
            val w = dictvar v;
            fun pr_superclass class =
              (Pretty.block o Pretty.breaks o map str) [
                label class, ":", "'" ^ v, deresolv class
              ];
            fun pr_classop (classop, ty) =
              (Pretty.block o Pretty.breaks) [
                (str o suffix "_" o NameSpace.base) classop, str ":", pr_typ NOBR ty
              ];
            fun pr_classop_fun (classop, _) =
              (Pretty.block o Pretty.breaks) [
                str "fun",
                (str o deresolv) classop,
                Pretty.enclose "(" ")" [str (w ^ ":'" ^ v ^ " " ^ deresolv class)],
                str "=",
                str ("#" ^ (suffix "_" o NameSpace.base) classop),
                str (w ^ ";")
              ];
          in
            Pretty.chunks (
              (Pretty.block o Pretty.breaks) [
                str ("type '" ^ v),
                (str o deresolv) class,
                str "=",
                Pretty.enum "," "{" "};" (
                  map pr_superclass superclasses @ map pr_classop classops
                )
              ]
              :: map pr_classop_fun classops
            )
          end
     | pr_def (MLClassinst (inst, ((class, (tyco, arity)), (superarities, classop_defs)))) =
          let
            fun pr_superclass (superclass, superinst_iss) =
              (Pretty.block o Pretty.breaks) [
                (str o label) superclass,
                str "=",
                pr_insts NOBR [Instance superinst_iss]
              ];
            fun pr_classop_def (classop, t) =
              let
                val consts = map_filter
                  (fn c => if (is_some o const_syntax) c
                    then NONE else (SOME o NameSpace.base o deresolv) c)
                    (CodegenThingol.fold_constnames (insert (op =)) t []);
                val vars = keyword_vars
                  |> intro_vars consts;
              in
                (Pretty.block o Pretty.breaks) [
                  (str o suffix "_" o NameSpace.base) classop,
                  str "=",
                  pr_term vars NOBR t
                ]
              end;
          in
            (Pretty.block o Pretty.breaks) ([
              str (if null arity then "val" else "fun"),
              (str o deresolv) inst ] @
              map pr_tyvar arity @ [
              str "=",
              Pretty.enum "," "{" "}" (map pr_superclass superarities @ map pr_classop_def classop_defs),
              str ":",
              pr_tycoexpr NOBR (class, [tyco `%% map (ITyVar o fst) arity])
            ])
          end;
  in pr_def ml_def end;



(** Haskell serializer **)

fun pr_haskell class_syntax tyco_syntax const_syntax keyword_vars deresolv_here deresolv def =
  let
    val is_cons = CodegenNames.has_nsp CodegenNames.nsp_dtco;
    fun class_name class = case class_syntax class
     of NONE => deresolv class
      | SOME (class, _) => class;
    fun classop_name class classop = case class_syntax class
     of NONE => NameSpace.base classop
      | SOME (_, classop_syntax) => case classop_syntax classop
         of NONE => NameSpace.base classop
          | SOME classop => classop
    fun pr_typparms tyvars vs =
      case maps (fn (v, sort) => map (pair v) sort) vs
       of [] => str ""
        | xs => Pretty.block [
            Pretty.enum "," "(" ")" (
              map (fn (v, class) => str
                (class_name class ^ " " ^ lookup_var tyvars v)) xs
            ),
            str " => "
          ];
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
                else pr fxy (pr_typ tyvars) tys)
      | pr_typ tyvars fxy (t1 `-> t2) =
          brackify_infix (1, R) fxy [
            pr_typ tyvars (INFX (1, X)) t1,
            str "->",
            pr_typ tyvars (INFX (1, R)) t2
          ]
      | pr_typ tyvars fxy (ITyVar v) =
          (str o lookup_var tyvars) v;
    fun pr_typscheme_expr tyvars (vs, tycoexpr) =
      Pretty.block [pr_typparms tyvars vs, pr_tycoexpr tyvars NOBR tycoexpr];
    fun pr_typscheme tyvars (vs, ty) =
      Pretty.block [pr_typparms tyvars vs, pr_typ tyvars NOBR ty];
    fun pr_term vars fxy (IConst c) =
          pr_app vars fxy (c, [])
      | pr_term vars fxy (t as (t1 `$ t2)) =
          (case CodegenThingol.unfold_const_app t
           of SOME app => pr_app vars fxy app
            | _ =>
                brackify fxy [
                  pr_term vars NOBR t1,
                  pr_term vars BR t2
                ])
      | pr_term vars fxy (IVar v) =
          (str o lookup_var vars) v
      | pr_term vars fxy (t as _ `|-> _) =
          let
            val (ts, t') = CodegenThingol.unfold_abs t;
            val vs = fold (CodegenThingol.fold_varnames (insert (op =)) o fst) ts [];
            val vars' = intro_vars vs vars;
          in
            brackify BR (
              str "\\"
              :: map (pr_term vars' BR o fst) ts @ [
              str "->",
              pr_term vars' NOBR t'
            ])
          end
      | pr_term vars fxy (INum (n, _)) =
          if n > 0 then
            (str o IntInf.toString) n
          else
            brackify BR [(str o Library.prefix "-" o IntInf.toString o IntInf.~) n]
      | pr_term vars fxy (IChar (c, _)) =
          (str o enclose "'" "'")
            (let val i = (Char.ord o the o Char.fromString) c
              in if i < 32
                then Library.prefix "\\" (string_of_int i)
                else c
              end)
      | pr_term vars fxy (t as ICase ((_, [_]), _)) =
          let
            val (ts, t) = CodegenThingol.unfold_let t;
            fun pr ((p, _), t) vars =
              let
                val vs = CodegenThingol.fold_varnames (insert (op =)) p [];
                val vars' = intro_vars vs vars;
              in
                ((Pretty.block o Pretty.breaks) [
                  pr_term vars' BR p,
                  str "=",
                  pr_term vars NOBR t
                ], vars')
              end;
            val (binds, vars') = fold_map pr ts vars;
          in Pretty.chunks [
            [str ("let"), Pretty.fbrk, binds |> Pretty.chunks] |> Pretty.block,
            [str ("in "), pr_term vars' NOBR t] |> Pretty.block
          ] end
      | pr_term vars fxy (ICase (((td, _), bs), _)) =
          let
            fun pr (p, t) =
              let
                val vs = CodegenThingol.fold_varnames (insert (op =)) p [];
                val vars' = intro_vars vs vars;
              in
                (Pretty.block o Pretty.breaks) [
                  pr_term vars' NOBR p,
                  str "->",
                  pr_term vars' NOBR t
                ]
              end
          in
            (Pretty.enclose "(" ")" o Pretty.breaks) [
              str "case",
              pr_term vars NOBR td,
              str "of",
              (Pretty.chunks o map pr) bs
            ]
          end
    and pr_app' vars c ts =
      (str o deresolv) c :: map (pr_term vars BR) ts
    and pr_app vars fxy =
      mk_app (pr_app' vars) (pr_term vars) const_syntax fxy;
    fun pr_def (name, CodegenThingol.Fun (funn as (eqs, (vs, ty)))) =
          let
            val tyvars = intro_vars (map fst vs) keyword_vars;
            fun pr_eq (ts, t) =
              let
                val consts = map_filter
                  (fn c => if (is_some o const_syntax) c
                    then NONE else (SOME o NameSpace.base o deresolv) c)
                    ((fold o CodegenThingol.fold_constnames) (insert (op =)) (t :: ts) []);
                val vars = keyword_vars
                  |> intro_vars consts
                  |> intro_vars ((fold o CodegenThingol.fold_unbound_varnames) (insert (op =)) (t :: ts) []);
              in
                (Pretty.block o Pretty.breaks) (
                  (str o deresolv_here) name
                  :: map (pr_term vars BR) ts
                  @ [str "=", pr_term vars NOBR t]
                )
              end;
          in
            Pretty.chunks (
              Pretty.block [
                (str o suffix " ::" o deresolv_here) name,
                Pretty.brk 1,
                pr_typscheme tyvars (vs, ty)
              ]
              :: (map pr_eq o fst o snd o constructive_fun) (name, funn)
            )
          end |> SOME
      | pr_def (name, CodegenThingol.Datatype (vs, [(co, [ty])])) =
          let
            val tyvars = intro_vars (map fst vs) keyword_vars;
          in
            (Pretty.block o Pretty.breaks) [
              str "newtype",
              pr_typscheme_expr tyvars (vs, (deresolv_here name, map (ITyVar o fst) vs)),
              str "=",
              (str o deresolv_here) co,
              pr_typ tyvars BR ty
            ]
          end |> SOME
      | pr_def (name, CodegenThingol.Datatype (vs, co :: cos)) =
          let
            val tyvars = intro_vars (map fst vs) keyword_vars;
            fun pr_co (co, tys) =
              (Pretty.block o Pretty.breaks) (
                (str o deresolv_here) co
                :: map (pr_typ tyvars BR) tys
              )
          in
            (Pretty.block o Pretty.breaks) (
              str "data"
              :: pr_typscheme_expr tyvars (vs, (deresolv_here name, map (ITyVar o fst) vs))
              :: str "="
              :: pr_co co
              :: map ((fn p => Pretty.block [str "| ", p]) o pr_co) cos
            )
          end |> SOME
      | pr_def (_, CodegenThingol.Datatypecons _) =
          NONE
      | pr_def (name, CodegenThingol.Class (superclasss, (v, classops))) =
          let
            val tyvars = intro_vars [v] keyword_vars;
            fun pr_classop (classop, ty) =
              Pretty.block [
                str (deresolv_here classop ^ " ::"),
                Pretty.brk 1,
                pr_typ tyvars NOBR ty
              ]
          in
            Pretty.block [
              str "class ",
              pr_typparms tyvars [(v, superclasss)],
              str (deresolv_here name ^ " " ^ v),
              str " where",
              Pretty.fbrk,
              Pretty.chunks (map pr_classop classops)
            ]
          end |> SOME
      | pr_def (_, CodegenThingol.Classmember _) =
          NONE
      | pr_def (_, CodegenThingol.Classinst ((class, (tyco, vs)), (_, classop_defs))) =
          let
            val tyvars = intro_vars (map fst vs) keyword_vars;
          in
            Pretty.block [
              str "instance ",
              pr_typparms tyvars vs,
              str (class_name class ^ " "),
              pr_typ tyvars BR (tyco `%% map (ITyVar o fst) vs),
              str " where",
              Pretty.fbrk,
              Pretty.chunks (map (fn (classop, t) =>
                let
                  val consts = map_filter
                    (fn c => if (is_some o const_syntax) c
                      then NONE else (SOME o NameSpace.base o deresolv) c)
                      (CodegenThingol.fold_constnames (insert (op =)) t []);
                  val vars = keyword_vars
                    |> intro_vars consts;
                in
                  (Pretty.block o Pretty.breaks) [
                    (str o classop_name class) classop,
                    str "=",
                    pr_term vars NOBR t
                  ]
                end
              ) classop_defs)
            ]
          end |> SOME
  in pr_def def end;


(** generic abstract serializer **)

structure NameMangler = NameManglerFun (
  type ctxt = (string * string -> string) * (string -> string option);
  type src = string * string;
  val ord = prod_ord string_ord string_ord;
  fun mk (postprocess, validate) ((shallow, name), 0) =
        let
          val name' = postprocess (shallow, name);
        in case validate name'
         of NONE => name'
          | _ => mk (postprocess, validate) ((shallow, name), 1)
        end
    | mk (postprocess, validate) (("", name), i) =
        postprocess ("", name ^ replicate_string i "'")
        |> perhaps validate
    | mk (postprocess, validate) ((shallow, name), 1) =
        postprocess (shallow, shallow ^ "_" ^ name)
        |> perhaps validate
    | mk (postprocess, validate) ((shallow, name), i) =
        postprocess (shallow, name ^ replicate_string i "'")
        |> perhaps validate;
  fun is_valid _ _ = true;
  fun maybe_unique _ _ = NONE;
  fun re_mangle _ dst = error ("No such definition name: " ^ quote dst);
);

(*FIXME refactor this properly*)
fun code_serialize seri_defs seri_module validate postprocess nsp_conn name_root
    (code : CodegenThingol.code) =
  let
    datatype node = Def of CodegenThingol.def | Module of node Graph.T;
    fun dest_modl (Module m) = m;
    fun dest_name name =
      let
        val (names, name_base) = (split_last o NameSpace.unpack) name;
        val (names_mod, name_shallow) = split_last names;
      in (names_mod, NameSpace.pack [name_shallow, name_base]) end;
    fun mk_deresolver module nsp_conn postprocess validate =
      let
        datatype tabnode = N of string * tabnode Symtab.table option;
        fun mk module manglers tab =
          let
            fun mk_name name =
              case NameSpace.unpack name
               of [n] => ("", n)
                | [s, n] => (s, n);
            fun in_conn (shallow, conn) =
              member (op = : string * string -> bool) conn shallow;
            fun add_name name =
              let
                val n as (shallow, _) = mk_name name;
              in
                AList.map_entry_yield in_conn shallow (
                  NameMangler.declare (postprocess, validate) n
                  #-> (fn n' => pair (name, n'))
                ) #> apfst the
              end;
            val (renamings, manglers') =
              fold_map add_name (Graph.keys module) manglers;
            fun extend_tab (n, n') =
              if (length o NameSpace.unpack) n = 1
              then
                Symtab.update_new
                  (n, N (n', SOME (mk ((dest_modl o Graph.get_node module) n) manglers' Symtab.empty)))
              else
                Symtab.update_new (n, N (n', NONE));
          in fold extend_tab renamings tab end;
        fun get_path_name [] tab =
              ([], SOME tab)
          | get_path_name [p] tab =
              let
                val SOME (N (p', tab')) = Symtab.lookup tab p
              in ([p'], tab') end
          | get_path_name [p1, p2] tab =
              (case Symtab.lookup tab p1
               of SOME (N (p', SOME tab')) =>
                    let
                      val (ps', tab'') = get_path_name [p2] tab'
                    in (p' :: ps', tab'') end
                | NONE =>
                    let
                      val SOME (N (p', NONE)) = Symtab.lookup tab (NameSpace.pack [p1, p2])
                    in ([p'], NONE) end)
          | get_path_name (p::ps) tab =
              let
                val SOME (N (p', SOME tab')) = Symtab.lookup tab p
                val (ps', tab'') = get_path_name ps tab'
              in (p' :: ps', tab'') end;
        fun deresolv tab prefix name =
          let
            val (common, (_, rem)) = chop_prefix (op =) (prefix, NameSpace.unpack name);
            val (_, SOME tab') = get_path_name common tab;
            val (name', _) = get_path_name rem tab';
          in NameSpace.pack name' end handle BIND => (error ("Missing name: " ^ quote name ^ ", in " ^ quote (NameSpace.pack prefix)));
      in deresolv (mk module (AList.make (K NameMangler.empty) nsp_conn) Symtab.empty) end;
    fun allimports_of modl =
      let
        fun imps_of prfx (Module modl) imps tab =
              let
                val this = NameSpace.pack prfx;
                val name_con = (rev o Graph.strong_conn) modl;
              in
                tab
                |> pair []
                |> fold (fn names => fn (imps', tab) =>
                    tab
                    |> fold_map (fn name =>
                         imps_of (prfx @ [name]) (Graph.get_node modl name) (imps' @ imps)) names
                    |-> (fn imps'' => pair (flat imps'' @ imps'))) name_con
                |-> (fn imps' =>
                   Symtab.update_new (this, imps' @ imps)
                #> pair (this :: imps'))
              end
          | imps_of prfx (Def _) imps tab =
              ([], tab);
      in snd (imps_of [] (Module modl) [] Symtab.empty) end;
    fun add_def ((names_mod, name_id), def) =
      let
        fun add [] =
              Graph.new_node (name_id, Def def)
          | add (m::ms) =
              Graph.default_node (m, Module Graph.empty)
              #> Graph.map_node m (Module o add ms o dest_modl)
      in add names_mod end;
    fun add_dep (name1, name2) =
      if name1 = name2 then I
      else
        let
          val m1 = dest_name name1 |> apsnd single |> (op @);
          val m2 = dest_name name2 |> apsnd single |> (op @);
          val (ms, (r1, r2)) = chop_prefix (op =) (m1, m2);
          val (ms, (s1::r1, s2::r2)) = chop_prefix (op =) (m1, m2);
          val add_edge =
            if null r1 andalso null r2
            then Graph.add_edge
            else fn edge => fn gr => (Graph.add_edge_acyclic edge gr
              handle Graph.CYCLES _ =>
                error ("Module dependency "
                  ^ quote name1 ^ " -> " ^ quote name2 ^ " would result in module dependency cycle"))
          fun add [] node =
                node
                |> add_edge (s1, s2)
            | add (m::ms) node =
                node
                |> Graph.map_node m (Module o add ms o dest_modl);
        in add ms end;
    val root_module = 
      Graph.empty
      |> Graph.fold (fn (name, (def, _)) => add_def (dest_name name, def)) code
      |> Graph.fold (fn (name, (_, (_, deps))) =>
          fold (curry add_dep name) deps) code;
    val names = map fst (Graph.dest root_module);
    val imptab = allimports_of root_module;
    val resolver = mk_deresolver root_module nsp_conn postprocess validate;
    fun sresolver s = (resolver o NameSpace.unpack) s
    fun mk_name prfx name =
      let
        val name_qual = NameSpace.pack (prfx @ [name])
      in (name_qual, resolver prfx name_qual) end;
    fun is_bot (_, (Def Bot)) = true
      | is_bot _ = false;
    fun mk_contents prfx module =
      map_filter (seri prfx)
        ((map (AList.make (Graph.get_node module)) o rev o Graph.strong_conn) module)
    and seri prfx [(name, Module modl)] =
          seri_module (resolver []) (map (resolver []) ((the o Symtab.lookup imptab) (NameSpace.pack (prfx @ [name]))))
            (mk_name prfx name, mk_contents (prfx @ [name]) modl)
      | seri prfx ds =
          seri_defs sresolver (NameSpace.pack prfx)
            (map (fn (name, Def def) => (fst (mk_name prfx name), def)) ds)
  in
    seri_module (resolver []) (map (resolver []) ((the o Symtab.lookup imptab) ""))
      (("", name_root), (mk_contents [] root_module))
  end;

fun abstract_serializer (target, nspgrp) name_root (from_defs, from_module, validator, postproc)
    postprocess (class_syntax, tyco_syntax, const_syntax)
    (drop, select) code =
  let
    fun project NONE code = code
      | project (SOME names) code =
          let
            fun check name = if member (op =) drop name
              then error ("shadowed definition " ^ quote name ^ " selected for serialization")
              else if can (Graph.get_node code) name
              then ()
              else error ("dropped definition " ^ quote name ^ " selected for serialization")
            val names' = (map o tap) check names;
          in CodegenThingol.project_code names code end;
    fun from_module' resolv imps ((name_qual, name), defs) =
      from_module resolv imps ((name_qual, name), defs)
      |> postprocess (resolv name_qual);
  in
    code
    |> tracing (fn _ => "dropping shadowed definitions...")
    |> CodegenThingol.delete_garbage drop
    |> tracing (fn _ => "projecting...")
    |> project select
    |> tracing (fn _ => "serializing...")
    |> code_serialize (from_defs (class_syntax, tyco_syntax, const_syntax))
         from_module' validator postproc nspgrp name_root
    |> K ()
  end;

fun abstract_validator keywords name =
  let
    fun replace_invalid c = (*FIXME*)
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

fun parse_args f args =
  case f args
   of (x, []) => x
    | (_, _) => error "bad serializer arguments";

fun parse_single_file serializer =
  parse_args (Args.name
  >> (fn path => serializer
        (fn "" => write_file false (Path.unpack path) #> K NONE
          | _ => SOME)));

fun parse_multi_file postprocess_module ext serializer =
  parse_args (Args.name
  >> (fn path => (serializer o mk_module_file postprocess_module ext) (Path.unpack path)));

fun parse_internal serializer =
  parse_args (Args.name
  >> (fn "-" => serializer
        (fn "" => (fn p => (use_text Output.ml_output false (Pretty.output p); NONE))
          | _ => SOME)
       | _ => Scan.fail ()));

fun parse_stdout serializer =
  parse_args (Args.name
  >> (fn "_" => serializer
        (fn "" => (fn p => (Pretty.writeln p; NONE))
          | _ => SOME)
       | _ => Scan.fail ()));

val nsp_module = CodegenNames.nsp_module;
val nsp_class = CodegenNames.nsp_class;
val nsp_tyco = CodegenNames.nsp_tyco;
val nsp_inst = CodegenNames.nsp_inst;
val nsp_fun = CodegenNames.nsp_fun;
val nsp_classop = CodegenNames.nsp_classop;
val nsp_dtco = CodegenNames.nsp_dtco;
val nsp_eval = CodegenNames.nsp_eval;


(** ML serializer **)

local

val reserved_ml' = [
  "bool", "int", "list", "unit", "option", "true", "false", "not",
  "NONE", "SOME", "o", "string", "char", "String", "Term"
];

fun ml_from_defs (_, tyco_syntax, const_syntax) deresolver prefx defs =
  let
    val seri = pr_sml_def tyco_syntax const_syntax
      (make_vars (ThmDatabase.ml_reserved @ reserved_ml'))
      (deresolver prefx) #> SOME;
    val filter_funs =
      map
        (fn (name, CodegenThingol.Fun info) => (name, info)
          | (name, def) => error ("Function block containing illegal def: " ^ quote name)
        )
      #> MLFuns;
    val filter_datatype =
      map_filter
        (fn (name, CodegenThingol.Datatype info) => SOME (name, info)
          | (name, CodegenThingol.Datatypecons _) => NONE
          | (name, def) => error ("Datatype block containing illegal def: " ^ quote name)
        )
      #> MLDatas;
    fun filter_class defs =
      case map_filter
        (fn (name, CodegenThingol.Class info) => SOME (name, info)
          | (name, CodegenThingol.Classmember _) => NONE
          | (name, def) => error ("Class block containing illegal def: " ^ quote name)
        ) defs
       of [class] => MLClass class
        | _ => error ("Class block without class: " ^ (commas o map (quote o fst)) defs)
  in case defs
   of (_, CodegenThingol.Fun _)::_ => (seri o filter_funs) defs
    | (_, CodegenThingol.Datatypecons _)::_ => (seri o filter_datatype) defs
    | (_, CodegenThingol.Datatype _)::_ => (seri o filter_datatype) defs
    | (_, CodegenThingol.Class _)::_ => (seri o filter_class) defs
    | (_, CodegenThingol.Classmember _)::_ => (seri o filter_class) defs
    | [(inst, CodegenThingol.Classinst info)] => seri (MLClassinst (inst, info))
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
    root_name (ml_from_defs, ml_from_module,
     abstract_validator (ThmDatabase.ml_reserved @ reserved_ml'), postproc) end;

in

fun ml_from_thingol target args =
  let
    val serializer = ml_serializer "ROOT" target [[nsp_module], [nsp_class, nsp_tyco],
      [nsp_fun, nsp_dtco, nsp_class, nsp_classop, nsp_inst]]
    val parse_multi =
      Args.name
      #-> (fn "dir" =>
               parse_multi_file
                 (K o SOME o str o suffix ";" o prefix "val _ = use "
                  o quote o suffix ".ML" o translate_string (fn "." => "/" | s => s)) "ML" serializer
            | _ => Scan.fail ());
  in
    (parse_multi
    || parse_internal serializer
    || parse_stdout serializer
    || parse_single_file serializer) args
  end;

val eval_verbose = ref false;

fun eval_term_proto thy data hidden ((ref_name, reff), e) code =
  let
    val (val_name, code') = CodegenThingol.add_eval_def (nsp_eval, e) code;
    val struct_name = "EVAL";
    fun output p = if !eval_verbose then (Pretty.writeln p; Pretty.output p)
      else Pretty.output p;
    val serializer = ml_serializer struct_name "SML" [[nsp_module], [nsp_class, nsp_tyco],
      [nsp_fun, nsp_dtco, nsp_class, nsp_classop, nsp_inst], [nsp_eval]]
      (fn "" => (fn p => (use_text Output.ml_output (!eval_verbose) (output p); NONE))
        | _ => SOME) data
        (hidden, SOME [NameSpace.pack [nsp_eval, val_name]]);
    val _ = serializer code';
    val val_name_struct = NameSpace.append struct_name val_name;
    val _ = reff := NONE;
    val _ = use_text Output.ml_output (!eval_verbose) ("val _ = (" ^ ref_name ^ " := SOME (" ^ val_name_struct ^ "))");
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

fun hs_from_thingol target args =
  let
    fun hs_from_defs keyword_vars (class_syntax, tyco_syntax, const_syntax) deresolver prefix defs =
      let
        val deresolv = deresolver "";
        val deresolv_here = deresolver prefix;
        val hs_from_def = pr_haskell class_syntax tyco_syntax const_syntax
          keyword_vars deresolv_here deresolv;
      in case map_filter hs_from_def defs
       of [] => NONE
        | ps => (SOME o Pretty.chunks o separate (str "")) ps
      end;
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
      "Main" (hs_from_defs (make_vars reserved_hs), hs_from_module, abstract_validator reserved_hs, postproc);
  in
    (parse_multi_file ((K o K) NONE) "hs" serializer) args
  end;


(** LEGACY DIAGNOSIS **)

local

open CodegenThingol;

in

val pretty_typparms =
  Pretty.list "(" ")" o Pretty.commas o map (fn (v, sort) => (Pretty.block o Pretty.breaks)
    [Pretty.str v, Pretty.str "::", Pretty.enum "&" "" "" (map Pretty.str sort)]);

fun pretty_itype (tyco `%% tys) =
      Pretty.enum "" "(" ")" (Pretty.str tyco :: map pretty_itype tys)
  | pretty_itype (ty1 `-> ty2) =
      Pretty.enum "" "(" ")" [pretty_itype ty1, Pretty.str "->", pretty_itype ty2]
  | pretty_itype (ITyVar v) =
      Pretty.str v;

fun pretty_iterm (IConst (c, _)) =
      Pretty.str c
  | pretty_iterm (IVar v) =
      Pretty.str ("?" ^ v)
  | pretty_iterm (t1 `$ t2) =
      (Pretty.enclose "(" ")" o Pretty.breaks)
        [pretty_iterm t1, pretty_iterm t2]
  | pretty_iterm ((v, ty) `|-> t) =
      (Pretty.enclose "(" ")" o Pretty.breaks)
        [Pretty.str v, Pretty.str "::", pretty_itype ty, Pretty.str "|->", pretty_iterm t]
  | pretty_iterm (INum (n, _)) =
      (Pretty.str o IntInf.toString) n
  | pretty_iterm (IChar (h, _)) =
      (Pretty.str o quote) h
  | pretty_iterm (ICase (((t, _), bs), _)) =
      (Pretty.enclose "(" ")" o Pretty.breaks) [
        Pretty.str "case",
        pretty_iterm t,
        Pretty.enclose "(" ")" (map (fn (p, t) =>
          (Pretty.block o Pretty.breaks) [
            pretty_iterm p,
            Pretty.str "=>",
            pretty_iterm t
          ]
        ) bs)
      ];

fun pretty_def Bot =
      Pretty.str "<Bot>"
  | pretty_def (Fun (eqs, (vs, ty))) =
      Pretty.enum " |" "" "" (
        map (fn (ps, body) =>
          Pretty.block [
            Pretty.enum "," "[" "]" (map pretty_iterm ps),
            Pretty.str " |->",
            Pretty.brk 1,
            pretty_iterm body,
            Pretty.str "::",
            pretty_typparms vs,
            Pretty.str "/",
            pretty_itype ty
          ]) eqs
        )
  | pretty_def (Datatype (vs, cs)) =
      Pretty.block [
        pretty_typparms vs,
        Pretty.str " |=> ",
        Pretty.enum " |" "" ""
          (map (fn (c, tys) => (Pretty.block o Pretty.breaks)
            (Pretty.str c :: map pretty_itype tys)) cs)
      ]
  | pretty_def (Datatypecons dtname) =
      Pretty.str ("cons " ^ dtname)
  | pretty_def (Class (supcls, (v, mems))) =
      Pretty.block [
        Pretty.str ("class var " ^ v ^ " extending "),
        Pretty.enum "," "[" "]" (map Pretty.str supcls),
        Pretty.str " with ",
        Pretty.enum "," "[" "]"
          (map (fn (m, ty) => Pretty.block
            [Pretty.str (m ^ "::"), pretty_itype ty]) mems)
      ]
  | pretty_def (Classmember clsname) =
      Pretty.block [
        Pretty.str "class member belonging to ",
        Pretty.str clsname
      ]
  | pretty_def (Classinst ((clsname, (tyco, arity)), _)) =
      Pretty.block [
        Pretty.str "class instance (",
        Pretty.str clsname,
        Pretty.str ", (",
        Pretty.str tyco,
        Pretty.str ", ",
        Pretty.enum "," "[" "]" (map (Pretty.enum "," "{" "}" o
          map Pretty.str o snd) arity),
        Pretty.str "))"
      ];

fun pretty_module code =
  Pretty.chunks (map (fn (name, def) => Pretty.block
    [Pretty.str name, Pretty.str " :=", Pretty.brk 1, pretty_def def])
    (AList.make (Graph.get_node code) (Graph.strong_conn code |> flat |> rev)));

fun pretty_deps code =
  let
    fun one_node key =
      let
        val preds_ = Graph.imm_preds code key;
        val succs_ = Graph.imm_succs code key;
        val mutbs = gen_inter (op =) (preds_, succs_);
        val preds = subtract (op =) mutbs preds_;
        val succs = subtract (op =) mutbs succs_;
      in
        (Pretty.block o Pretty.fbreaks) (
          Pretty.str key
          :: map (fn s => Pretty.str ("<-> " ^ s)) mutbs
          @ map (fn s => Pretty.str ("<-- " ^ s)) preds
          @ map (fn s => Pretty.str ("--> " ^ s)) succs
        )
      end
  in
    code
    |> Graph.strong_conn
    |> flat
    |> rev
    |> map one_node
    |> Pretty.chunks
  end;

end; (*local*)



(** theory data **)

datatype syntax_expr = SyntaxExpr of {
  class: ((string * (string -> string option)) * serial) Symtab.table,
  inst: unit Symtab.table,
  tyco: (itype pretty_syntax * serial) Symtab.table,
  const: (iterm pretty_syntax * serial) Symtab.table
};

fun mk_syntax_expr ((class, inst), (tyco, const)) =
  SyntaxExpr { class = class, inst = inst, tyco = tyco, const = const };
fun map_syntax_expr f (SyntaxExpr { class, inst, tyco, const }) =
  mk_syntax_expr (f ((class, inst), (tyco, const)));
fun merge_syntax_expr (SyntaxExpr { class = class1, inst = inst1, tyco = tyco1, const = const1 },
    SyntaxExpr { class = class2, inst = inst2, tyco = tyco2, const = const2 }) =
  mk_syntax_expr (
    (Symtab.merge (eq_snd (op =)) (class1, class2),
       Symtab.merge (op =) (inst1, inst2)),
    (Symtab.merge (eq_snd (op =)) (tyco1, tyco2),
       Symtab.merge (eq_snd (op =)) (const1, const2))
  );

datatype syntax_modl = SyntaxModl of {
  merge: string Symtab.table,
  prolog: Pretty.T Symtab.table
};

fun mk_syntax_modl (merge, prolog) =
  SyntaxModl { merge = merge, prolog = prolog };
fun map_syntax_modl f (SyntaxModl { merge, prolog }) =
  mk_syntax_modl (f (merge, prolog));
fun merge_syntax_modl (SyntaxModl { merge = merge1, prolog = prolog1 },
    SyntaxModl { merge = merge2, prolog = prolog2 }) =
  mk_syntax_modl (
    Symtab.merge (op =) (merge1, merge2),
    Symtab.merge (op =) (prolog1, prolog2)
  );

type serializer = string -> Args.T list
-> (string -> (string * (string -> string option)) option)
   * (string
      -> (int
          * (fixity
             -> (fixity
                 -> itype -> Pretty.T)
                -> itype list -> Pretty.T)) 
           option)
   * (string
      -> (int
          * (fixity
             -> (fixity
                 -> iterm -> Pretty.T)
                -> iterm list -> Pretty.T)) 
           option)
   -> string list * string list option
      -> CodegenThingol.code -> unit;

datatype target = Target of {
  serial: serial,
  serializer: serializer,
  syntax_expr: syntax_expr,
  syntax_modl: syntax_modl
};

fun mk_target (serial, (serializer, (syntax_expr, syntax_modl))) =
  Target { serial = serial, serializer = serializer, syntax_expr = syntax_expr, syntax_modl = syntax_modl };
fun map_target f ( Target { serial, serializer, syntax_expr, syntax_modl } ) =
  mk_target (f (serial, (serializer, (syntax_expr, syntax_modl))));
fun merge_target target (Target { serial = serial1, serializer = serializer, syntax_expr = syntax_expr1, syntax_modl = syntax_modl1 },
    Target { serial = serial2, serializer = _, syntax_expr = syntax_expr2, syntax_modl = syntax_modl2 }) =
  if serial1 = serial2 then
    mk_target (serial1, (serializer,
      (merge_syntax_expr (syntax_expr1, syntax_expr2),
        merge_syntax_modl (syntax_modl1, syntax_modl2))
    ))
  else
    error ("Incompatible serializers: " ^ quote target);

structure CodegenSerializerData = TheoryDataFun
(struct
  val name = "Pure/codegen_serializer";
  type T = target Symtab.table;
  val empty = Symtab.empty;
  val copy = I;
  val extend = I;
  fun merge _ = Symtab.join merge_target;
  fun print _ _ = ();
end);

fun the_serializer (Target { serializer, ... }) = serializer;
fun the_syntax_expr (Target { syntax_expr = SyntaxExpr x, ... }) = x;
fun the_syntax_modl (Target { syntax_modl = SyntaxModl x, ... }) = x;

fun add_serializer (target, seri) thy =
  let
    val _ = case Symtab.lookup (CodegenSerializerData.get thy) target
     of SOME _ => warning ("overwriting existing serializer " ^ quote target)
      | NONE => ();
  in
    thy
    |> (CodegenSerializerData.map oo Symtab.map_default)
          (target, mk_target (serial (), (seri,
            (mk_syntax_expr ((Symtab.empty, Symtab.empty), (Symtab.empty, Symtab.empty)),
              mk_syntax_modl (Symtab.empty, Symtab.empty)))))
          (map_target (fn (serial, (_, syntax)) => (serial, (seri, syntax))))
  end;

val _ = Context.add_setup (
  CodegenSerializerData.init
  #> add_serializer ("SML", ml_from_thingol)
  #> add_serializer ("Haskell", hs_from_thingol)
);

fun get_serializer thy (target, args) cs =
  let
    val data = case Symtab.lookup (CodegenSerializerData.get thy) target
     of SOME data => data
      | NONE => error ("Unknown code target language: " ^ quote target);
    val seri = the_serializer data;
    val { class, inst, tyco, const } = the_syntax_expr data;
    fun fun_of sys = (Option.map fst oo Symtab.lookup) sys;
  in
    seri target args (fun_of class, fun_of tyco, fun_of const)
      (Symtab.keys class @ Symtab.keys inst @ Symtab.keys tyco @ Symtab.keys const, cs)
  end;

fun has_serialization f thy targets name =
  forall (
    is_some o (fn tab => Symtab.lookup tab name) o f o the_syntax_expr o the
      o (Symtab.lookup ((CodegenSerializerData.get) thy))
  ) targets;

val tyco_has_serialization = has_serialization #tyco;
val const_has_serialization = has_serialization #const;

fun eval_term thy =
  let
    val target = "SML";
    val data = case Symtab.lookup (CodegenSerializerData.get thy) target
     of SOME data => data
      | NONE => error ("Unknown code target language: " ^ quote target);
    val { class, inst, tyco, const } = the_syntax_expr data;
    fun fun_of sys = (Option.map fst oo Symtab.lookup) sys;
  in
    eval_term_proto thy (fun_of class, fun_of tyco, fun_of const)
      (Symtab.keys class @ Symtab.keys inst @ Symtab.keys tyco @ Symtab.keys const)
  end;



(** target syntax interfaces **)

local

fun map_syntax_exprs target f thy =
  let
    val _ = if is_some (Symtab.lookup (CodegenSerializerData.get thy) target)
      then ()
      else error ("Unknown code target language: " ^ quote target);
  in
    thy
    |> (CodegenSerializerData.map o Symtab.map_entry target o map_target
          o apsnd o apsnd o apfst o map_syntax_expr) f
  end;

fun gen_add_syntax_class prep_class prep_const target raw_class (syntax, raw_ops) thy =
  let
    val cls = prep_class thy raw_class
    val class = CodegenNames.class thy cls;
    fun mk_classop (const as (c, _)) = case AxClass.class_of_param thy c
     of SOME class' => if cls = class' then CodegenNames.const thy const
          else error ("Not a class operation for class " ^ quote class ^ ": " ^ quote c)
      | NONE => error ("Not a class operation: " ^ quote c)
    val ops = (map o apfst) (mk_classop o prep_const thy) raw_ops;
    val syntax_ops = AList.lookup (op =) ops;
  in
    thy
    |> (map_syntax_exprs target o apfst o apfst)
        (Symtab.update (class, ((syntax, syntax_ops), serial ())))
  end;

fun gen_add_syntax_inst prep_class prep_tyco target (raw_tyco, raw_class) thy =
  let
    val inst = CodegenNames.instance thy (prep_class thy raw_class, prep_tyco thy raw_tyco);
  in
    thy
    |> (map_syntax_exprs target o apfst o apsnd)
        (Symtab.update (inst, ()))
  end;

fun gen_add_syntax_tyco prep_tyco raw_tyco target syntax thy =
  let
    val tyco = (CodegenNames.tyco thy o prep_tyco thy) raw_tyco;
  in
    thy
    |> (map_syntax_exprs target o apsnd o apfst)
         (Symtab.update (tyco, (syntax, serial ())))
  end;

fun gen_add_syntax_const prep_const raw_c target syntax thy =
  let
    val c' = prep_const thy raw_c;
    val c'' = CodegenNames.const thy c';
  in
    thy
    |> (map_syntax_exprs target o apsnd o apsnd)
         (Symtab.update (c'', (syntax, serial ())))
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
