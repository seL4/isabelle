(*  Title:      Pure/Tools/codegen_serializer.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Serializer from intermediate language ("Thin-gol") to
target languages (like SML or Haskell).
*)

signature CODEGEN_SERIALIZER =
sig
  include BASIC_CODEGEN_THINGOL;

  val add_pretty_list: string -> string -> string -> (Pretty.T list -> Pretty.T)
   -> ((string -> string) * (string -> string)) option -> int * string
   -> theory -> theory;
  val add_pretty_ml_string: string -> string -> string -> string
   -> (string -> string) -> (string -> string) -> string -> theory -> theory;
  val add_undefined: string -> string -> string -> theory -> theory;

  type serializer;
  val add_serializer : string * serializer -> theory -> theory;
  val ml_from_thingol: serializer;
  val hs_from_thingol: serializer;
  val get_serializer: theory -> string -> Args.T list
    -> string list option -> CodegenThingol.code -> unit;

  val const_has_serialization: theory -> string list -> string -> bool;
  val tyco_has_serialization: theory -> string list -> string -> bool;

  val eval_verbose: bool ref;
  val eval_term: theory ->
    (string * 'a option ref) * CodegenThingol.iterm -> CodegenThingol.code
    -> 'a;
  val sml_code_width: int ref;
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

fun mk_app mk_app' from_expr const_syntax fxy (app as ((c, (_, ty)), ts)) =
  case const_syntax c
   of NONE => brackify fxy (mk_app' app)
    | SOME (i, pr) =>
        let
          val k = if i < 0 then (length o fst o CodegenThingol.unfold_fun) ty else i
        in if k <= length ts
          then case chop i ts of (ts1, ts2) =>
            brackify fxy (pr fxy from_expr ts1 :: map (from_expr BR) ts2)
          else from_expr fxy (CodegenThingol.eta_expand app k)
        end;

val first_upper = implode o nth_map 0 Symbol.to_ascii_upper o explode;


(* user-defined syntax *)

val str = setmp print_mode [] Pretty.str;

val (atomK, infixK, infixlK, infixrK) =
  ("target_atom", "infix", "infixl", "infixr");
val _ = OuterSyntax.add_keywords [atomK, infixK, infixlK, infixrK];

datatype 'a mixfix =
    Arg of fixity
  | Pretty of Pretty.T;

fun fillin_mixfix fxy_this ms fxy_ctxt pr args =
  let
    fun fillin [] [] =
          []
      | fillin (Arg fxy :: ms) (a :: args) =
          pr fxy a :: fillin ms args
      | fillin (Pretty p :: ms) args =
          p :: fillin ms args
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
    [Arg l, (Pretty o Pretty.brk) 1, (Pretty o str) s, (Pretty o Pretty.brk) 1, Arg r]
  end;

fun parse_mixfix s =
  let
    val sym_any = Scan.one Symbol.not_eof;
    val parse = Scan.repeat (
         ($$ "_" -- $$ "_" >> K (Arg NOBR))
      || ($$ "_" >> K (Arg BR))
      || ($$ "/" |-- Scan.repeat ($$ " ") >> (Pretty o Pretty.brk o length))
      || (Scan.repeat1
           (   $$ "'" |-- sym_any
            || Scan.unless ($$ "_" || $$ "/")
                 sym_any) >> (Pretty o str o implode)));
  in case Scan.finite Symbol.stopper parse (Symbol.explode s)
   of (p, []) => p
    | _ => Scan.fail_with (fn _ => "Malformed mixfix annotation: " ^ quote s) ()
  end;

fun parse_syntax tokens =
  let
    fun is_arg (Arg _) = true
      | is_arg _ = false;
    fun parse_nonatomic s =
      case parse_mixfix s
       of [Pretty _] =>
            Scan.fail_with (fn _ => "Mixfix contains just one pretty element; either declare as "
              ^ quote atomK ^ " or consider adding a break") ()
        | x => x;
    fun mk fixity mfx =
      let
        val i = (length o List.filter is_arg) mfx;
      in (i, fillin_mixfix fixity mfx) end;
    val parse = (
           OuterParse.$$$ infixK  |-- OuterParse.nat
            >> (fn i => (parse_infix (INFX (i, X)), INFX (i, X)))
        || OuterParse.$$$ infixlK |-- OuterParse.nat
            >> (fn i => (parse_infix (INFX (i, L)), INFX (i, L)))
        || OuterParse.$$$ infixrK |-- OuterParse.nat
            >> (fn i => (parse_infix (INFX (i, R)), INFX (i, R)))
        || OuterParse.$$$ atomK |-- pair (parse_mixfix, NOBR)
        || pair (parse_nonatomic, BR)
      ) -- OuterParse.string >> (fn ((p, fxy), s) => (p s, fxy));
  in
    (parse >> (fn (mfx, fixity) => mk fixity mfx)) tokens
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
  then (SOME o str o mk_string o implode o map (fn IChar c => mk_char c)) es
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
                brackify fxy [pr_term vars NOBR t1, pr_term vars BR t2])
      | pr_term vars fxy (t as _ `|-> _) =
          let
            val (ps, t') = CodegenThingol.unfold_abs t;
            fun pr ((v, NONE), _) vars =
                  let
                    val vars' = intro_vars [v] vars;
                  in
                    ((Pretty.block o Pretty.breaks) [str "fn", str (lookup_var vars' v), str "=>"], vars')
                  end
              | pr ((v, SOME p), _) vars =
                  let
                    val vs = CodegenThingol.fold_varnames (insert (op =)) p [v];
                    val vars' = intro_vars vs vars;
                  in
                    ((Pretty.block o Pretty.breaks) [str "fn", str (lookup_var vars' v), str "as",
                      pr_term vars' NOBR p, str "=>"], vars')
                  end;
            val (ps', vars') = fold_map pr ps vars;
          in brackify BR (ps' @ [pr_term vars' NOBR t']) end
      | pr_term vars fxy (INum n) =
          brackify BR [(str o IntInf.toString) n, str ":", str "IntInf.int"]
      | pr_term vars _ (IChar c) =
          (str o prefix "#" o quote)
            (let val i = ord c
              in if i < 32
                then prefix "\\" (string_of_int i)
                else c
              end)
      | pr_term vars fxy (t as ICase (_, [_])) =
          let
            val (ts, t') = CodegenThingol.unfold_let t;
            fun mk ((p, _), t'') vars =
              let
                val vs = CodegenThingol.fold_varnames (insert (op =)) p [];
                val vars' = intro_vars vs vars;
              in
                (Pretty.block [
                  (Pretty.block o Pretty.breaks) [
                    str "val",
                    pr_term vars' NOBR p,
                    str "=",
                    pr_term vars NOBR t''
                  ],
                  str ";"
                ], vars')
              end
            val (binds, vars') = fold_map mk ts vars;
          in
            Pretty.chunks [
              [str ("let"), Pretty.fbrk, binds |> Pretty.chunks] |> Pretty.block,
              [str ("in"), Pretty.fbrk, pr_term vars' NOBR t'] |> Pretty.block,
              str ("end")
            ] end
      | pr_term vars fxy (ICase ((td, ty), b::bs)) =
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
    and pr_app' vars (app as ((c, (iss, ty)), ts)) =
      if is_cons c then let
        val k = (length o fst o CodegenThingol.unfold_fun) ty
      in if k < 2 then 
        (str o deresolv) c :: map (pr_term vars BR) ts
      else if k = length ts then
        [(str o deresolv) c, Pretty.enum "," "(" ")" (map (pr_term vars NOBR) ts)]
      else [pr_term vars BR (CodegenThingol.eta_expand app k)] end else
        (str o deresolv) c :: map (pr_term vars BR) ts
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
            val (ps, t') = CodegenThingol.unfold_abs t;
            fun pr ((v, SOME p), _) vars =
                  let
                    val vs = CodegenThingol.fold_varnames (insert (op =)) p [v];
                    val vars' = intro_vars vs vars;
                  in ((Pretty.block o Pretty.breaks) [str (lookup_var vars' v), str "@", pr_term vars' BR p], vars') end
              | pr ((v, NONE), _) vars =
                  let
                    val vars' = intro_vars [v] vars;
                  in (str (lookup_var vars' v), vars') end;
            val (ps', vars') = fold_map pr ps vars;
          in
            brackify BR (
              str "\\"
              :: ps' @ [
              str "->",
              pr_term vars' NOBR t'
            ])
          end
      | pr_term vars fxy (INum n) =
          if n > 0 then
            (str o IntInf.toString) n
          else
            brackify BR [(str o Library.prefix "-" o IntInf.toString o IntInf.~) n]
      | pr_term vars fxy (IChar c) =
          (str o enclose "'" "'")
            (let val i = (Char.ord o the o Char.fromString) c
              in if i < 32
                then Library.prefix "\\" (string_of_int i)
                else c
              end)
      | pr_term vars fxy (t as ICase (_, [_])) =
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
      | pr_term vars fxy (ICase ((td, _), bs)) =
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
    and pr_app' vars ((c, _), ts) =
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
      | pr_def (_, CodegenThingol.Bot) =
          NONE;
  in pr_def def end;

val reserved_haskell = [
  "hiding", "deriving", "where", "case", "of", "infix", "infixl", "infixr",
  "import", "default", "forall", "let", "in", "class", "qualified", "data",
  "newtype", "instance", "if", "then", "else", "type", "as", "do", "module"
];

fun seri_haskell module_prefix destination reserved_user module_alias module_prolog
  class_syntax tyco_syntax const_syntax code =
  let
    val init_vars = make_vars (reserved_haskell @ reserved_user);
  in () end;



(** diagnosis serializer **)

fun seri_diagnosis _ _ _ _ _ code =
  let
    val init_vars = make_vars reserved_haskell;
    val pr = pr_haskell (K NONE) (K NONE) (K NONE) init_vars I I;
  in
    []
    |> Graph.fold (fn (name, (def, _)) =>
        case pr (name, def) of SOME p => cons p | NONE => I) code
    |> separate (Pretty.str "")
    |> Pretty.chunks
    |> Pretty.writeln
  end;



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

fun abstract_serializer nspgrp name_root (from_defs, from_module, validator, postproc)
    postprocess
    reserved_user module_alias module_prolog class_syntax tyco_syntax const_syntax
    code =
  let
    fun from_module' resolv imps ((name_qual, name), defs) =
      from_module resolv imps ((name_qual, name), defs)
      |> postprocess (resolv name_qual);
  in
    code_serialize (from_defs (class_syntax, tyco_syntax, const_syntax))
      from_module' validator postproc nspgrp name_root code
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
    |> Pretty.setmp_margin 999999 (write_file true (Path.append prfx name'))
    |> postprocess_module name
  end;

fun parse_args f args =
  case f args
   of (x, []) => x
    | (_, _) => error "bad serializer arguments";

val sml_code_width = ref 80;

fun parse_single_file serializer =
  parse_args (Args.name
  >> (fn path => serializer
        (fn "" => Pretty.setmp_margin (!sml_code_width) (write_file false (Path.unpack path)) #> K NONE
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

fun ml_serializer root_name nspgrp =
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
  in abstract_serializer nspgrp
    root_name (ml_from_defs, ml_from_module,
     abstract_validator (ThmDatabase.ml_reserved @ reserved_ml'), postproc) end;

in

fun ml_from_thingol args =
  let
    val serializer = ml_serializer "ROOT" [[nsp_module], [nsp_class, nsp_tyco],
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

fun eval_term_proto thy data1 data2 data3 data4 data5 data6 hidden ((ref_name, reff), e) code =
  let
    val (val_name, code') = CodegenThingol.add_eval_def (nsp_eval, e) code;
    val code'' = CodegenThingol.project_code hidden (SOME [NameSpace.pack [nsp_eval, val_name]]) code';
    val struct_name = "EVAL";
    fun output p = if !eval_verbose then (Pretty.writeln p; Pretty.output p)
      else Pretty.output p;
    val serializer = ml_serializer struct_name [[nsp_module], [nsp_class, nsp_tyco],
      [nsp_fun, nsp_dtco, nsp_class, nsp_classop, nsp_inst], [nsp_eval]]
      (fn "" => (fn p => (use_text Output.ml_output (!eval_verbose) (output p); NONE))
        | _ => SOME) data1 data2 data3 data4 data5 data6;
    val _ = serializer code'';
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

fun hs_from_thingol args =
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
    val serializer = abstract_serializer [[nsp_module],
      [nsp_class], [nsp_tyco], [nsp_fun, nsp_classop], [nsp_dtco], [nsp_inst]]
      "Main" (hs_from_defs (make_vars reserved_hs), hs_from_module, abstract_validator reserved_hs, postproc);
  in
    (parse_multi_file ((K o K) NONE) "hs" serializer) args
  end;



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
  alias: string Symtab.table,
  prolog: Pretty.T Symtab.table
};

fun mk_syntax_modl (alias, prolog) =
  SyntaxModl { alias = alias, prolog = prolog };
fun map_syntax_modl f (SyntaxModl { alias, prolog }) =
  mk_syntax_modl (f (alias, prolog));
fun merge_syntax_modl (SyntaxModl { alias = alias1, prolog = prolog1 },
    SyntaxModl { alias = alias2, prolog = prolog2 }) =
  mk_syntax_modl (
    Symtab.merge (op =) (alias1, alias2),
    Symtab.merge (op =) (prolog1, prolog2)
  );

type serializer = Args.T list
  -> string list
  -> (string -> string option)
  -> (string -> Pretty.T option)
  -> (string -> (string * (string -> string option)) option)
  -> (string -> (int * (fixity -> (fixity -> itype -> Pretty.T) -> itype list -> Pretty.T)) option)
  -> (string -> (int * (fixity -> (fixity -> iterm -> Pretty.T) -> iterm list -> Pretty.T))  option)
  -> CodegenThingol.code -> unit;

datatype target = Target of {
  serial: serial,
  serializer: serializer,
  syntax_expr: syntax_expr,
  syntax_modl: syntax_modl,
  reserved: string list
};

fun mk_target (serial, ((serializer, reserved), (syntax_expr, syntax_modl))) =
  Target { serial = serial, reserved = reserved, serializer = serializer, syntax_expr = syntax_expr, syntax_modl = syntax_modl };
fun map_target f ( Target { serial, serializer, reserved, syntax_expr, syntax_modl } ) =
  mk_target (f (serial, ((serializer, reserved), (syntax_expr, syntax_modl))));
fun merge_target target (Target { serial = serial1, serializer = serializer, reserved = reserved1,
  syntax_expr = syntax_expr1, syntax_modl = syntax_modl1 },
    Target { serial = serial2, serializer = _, reserved = reserved2,
      syntax_expr = syntax_expr2, syntax_modl = syntax_modl2 }) =
  if serial1 = serial2 then
    mk_target (serial1, ((serializer, merge (op =) (reserved1, reserved2)),
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
fun the_reserved (Target { reserved, ... }) = reserved;
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
          (target, mk_target (serial (), ((seri, []),
            (mk_syntax_expr ((Symtab.empty, Symtab.empty), (Symtab.empty, Symtab.empty)),
              mk_syntax_modl (Symtab.empty, Symtab.empty)))))
          (map_target (fn (serial, ((_, keywords), syntax)) => (serial, ((seri, keywords), syntax))))
  end;

fun map_seri_data target f thy =
  let
    val _ = if is_some (Symtab.lookup (CodegenSerializerData.get thy) target)
      then ()
      else error ("Unknown code target language: " ^ quote target);
  in
    thy
    |> (CodegenSerializerData.map o Symtab.map_entry target o map_target) f
  end;

val target_diag = "diag";

val _ = Context.add_setup (
  CodegenSerializerData.init
  #> add_serializer ("SML", ml_from_thingol)
  #> add_serializer ("Haskell", hs_from_thingol)
  #> add_serializer (target_diag, (fn _ => fn _ => seri_diagnosis))
);

fun get_serializer thy target args cs =
  let
    val data = case Symtab.lookup (CodegenSerializerData.get thy) target
     of SOME data => data
      | NONE => error ("Unknown code target language: " ^ quote target);
    val seri = the_serializer data;
    val reserved = the_reserved data;
    val { alias, prolog } = the_syntax_modl data;
    val { class, inst, tyco, const } = the_syntax_expr data;
    fun fun_of sys = (Option.map fst oo Symtab.lookup) sys;
    val project = if target = target_diag then I
      else CodegenThingol.project_code
        (Symtab.keys class @ Symtab.keys inst @ Symtab.keys tyco @ Symtab.keys const) cs;
  in
    project #> seri args reserved (Symtab.lookup alias) (Symtab.lookup prolog)
      (fun_of class) (fun_of tyco) (fun_of const)
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
    val reserved = the_reserved data;
    val { alias, prolog } = the_syntax_modl data;
    val { class, inst, tyco, const } = the_syntax_expr data;
    fun fun_of sys = (Option.map fst oo Symtab.lookup) sys;
  in
    eval_term_proto thy reserved (Symtab.lookup alias) (Symtab.lookup prolog) (fun_of class) (fun_of tyco) (fun_of const)
      (Symtab.keys class @ Symtab.keys inst @ Symtab.keys tyco @ Symtab.keys const)
  end;



(** ML and toplevel interface **)

local

fun map_syntax_exprs target =
  map_seri_data target o (apsnd o apsnd o apfst o map_syntax_expr);
fun map_syntax_modls target =
  map_seri_data target o (apsnd o apsnd o apsnd o map_syntax_modl);
fun map_reserveds target =
  map_seri_data target o (apsnd o apfst o apsnd);

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

fun gen_add_syntax_tyco prep_tyco target raw_tyco (syntax as (n, _)) thy =
  let
    val tyco = prep_tyco thy raw_tyco;
    val tyco' = CodegenNames.tyco thy tyco;
    val _ = if n > Sign.arity_number thy tyco
      then error ("Too many arguments in syntax for type constructor " ^ quote tyco)
      else ()
  in
    thy
    |> (map_syntax_exprs target o apsnd o apfst)
         (Symtab.update (tyco', (syntax, serial ())))
  end;

fun gen_add_syntax_const prep_const target raw_c (syntax as (n, _)) thy =
  let
    val c = prep_const thy raw_c;
    val c' = CodegenNames.const thy c;
    val _ = if n > (length o fst o strip_type o Sign.the_const_type thy o fst) c
      then error ("Too many arguments in syntax for constant " ^ (quote o fst) c)
      else ()
  in
    thy
    |> (map_syntax_exprs target o apsnd o apsnd)
         (Symtab.update (c', (syntax, serial ())))
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

val add_syntax_class = gen_add_syntax_class ClassPackage.read_class CodegenConsts.read_const;
val add_syntax_inst = gen_add_syntax_inst ClassPackage.read_class read_type;
val add_syntax_tyco = gen_add_syntax_tyco read_type;
val add_syntax_const = gen_add_syntax_const CodegenConsts.read_const;

fun add_reserved target =
  map_reserveds target o insert (op =);

fun add_modl_alias target =
  map_syntax_modls target o apfst o Symtab.update o apsnd CodegenNames.check_modulename;

fun add_modl_prolog target =
  map_syntax_modls target o apsnd o
    (fn (modl, NONE) => Symtab.delete modl | (modl, SOME prolog) =>
      Symtab.update (modl, Pretty.str prolog));

fun zip_list (x::xs) f g =
  f
  #-> (fn y =>
    fold_map (fn x => g |-- f >> pair x) xs
    #-> (fn xys => pair ((x, y) :: xys)));

structure P = OuterParse
and K = OuterKeyword

fun parse_multi_syntax parse_thing parse_syntax =
  P.and_list1 parse_thing
  #-> (fn things => Scan.repeat1 (P.$$$ "(" |-- P.name --
        (zip_list things parse_syntax (P.$$$ "and")) --| P.$$$ ")"));

val (code_classK, code_instanceK, code_typeK, code_constK,
  code_reservedK, code_modulenameK, code_moduleprologK) =
  ("code_class", "code_instance", "code_type", "code_const",
    "code_reserved", "code_modulename", "code_moduleprolog");

in

fun add_pretty_list target nill cons mk_list mk_char_string target_cons thy =
  let
    val [(_, nil''), (cons', cons'')] = idfs_of_const_names thy [nill, cons];
    val pr = pretty_list nil'' cons'' mk_list mk_char_string target_cons;
  in
    thy
    |> gen_add_syntax_const (K I) target cons' pr
  end;

fun add_pretty_ml_string target nill cons str mk_char mk_string target_implode thy =
  let
    val [(_, nil''), (_, cons''), (str', _)] = idfs_of_const_names thy [nill, cons, str];
    val pr = pretty_ml_string nil'' cons'' mk_char mk_string target_implode;
  in
    thy
    |> gen_add_syntax_const (K I) target str' pr
  end;

fun add_undefined target undef target_undefined thy =
  let
    val [(undef', _)] = idfs_of_const_names thy [undef];
    fun pretty _ _ _ = str target_undefined;
  in
    thy
    |> gen_add_syntax_const (K I) target undef' (~1, pretty)
  end;

val code_classP =
  OuterSyntax.command code_classK "define code syntax for class" K.thy_decl (
    parse_multi_syntax P.xname
      (P.string -- Scan.optional (P.$$$ "where" |-- Scan.repeat1
        (P.term --| (P.$$$ "\\<equiv>" || P.$$$ "==") -- P.string)) [])
    >> (Toplevel.theory oo fold) (fn (target, syns) =>
          fold (fn (raw_class, syn) => add_syntax_class target raw_class syn) syns)
  );

val code_instanceP =
  OuterSyntax.command code_instanceK "define code syntax for instance" K.thy_decl (
    parse_multi_syntax (P.xname --| P.$$$ "::" -- P.xname)
      (P.name #->
        (fn "-" => Scan.succeed () | _ => Scan.fail_with (fn _ => "\"-\" expected") ()))
    >> (Toplevel.theory oo fold) (fn (target, syns) =>
          fold (fn (raw_inst, ()) => add_syntax_inst target raw_inst) syns)
  );

val code_typeP =
  OuterSyntax.command code_typeK "define code syntax for type constructor" K.thy_decl (
    parse_multi_syntax P.xname parse_syntax
    >> (Toplevel.theory oo fold) (fn (target, syns) =>
          fold (fn (raw_tyco, syn) => add_syntax_tyco target raw_tyco syn) syns)
  );

val code_constP =
  OuterSyntax.command code_constK "define code syntax for constant" K.thy_decl (
    parse_multi_syntax P.term parse_syntax
    >> (Toplevel.theory oo fold) (fn (target, syns) =>
          fold (fn (raw_const, syn) => add_syntax_const target raw_const syn) syns)
  );

val code_reservedP =
  OuterSyntax.command code_reservedK "declare words as reserved for target language" K.thy_decl (
    P.name -- Scan.repeat1 P.name
    >> (fn (target, reserveds) => (Toplevel.theory o fold (add_reserved target)) reserveds)
  )

val code_modulenameP =
  OuterSyntax.command code_reservedK "alias module to other name" K.thy_decl (
    P.name -- Scan.repeat1 (P.name -- P.name)
    >> (fn (target, modlnames) => (Toplevel.theory o fold (add_modl_alias target)) modlnames)
  )

val code_moduleprologP =
  OuterSyntax.command code_reservedK "add prolog to module" K.thy_decl (
    P.name -- Scan.repeat1 (P.name -- (P.string >> (fn "-" => NONE | s => SOME s)))
    >> (fn (target, prologs) => (Toplevel.theory o fold (add_modl_prolog target)) prologs)
  )

val _ = OuterSyntax.add_parsers [code_classP, code_instanceP, code_typeP, code_constP,
  code_reservedP, code_modulenameP, code_moduleprologP];

end; (*local*)

end; (* struct *)
