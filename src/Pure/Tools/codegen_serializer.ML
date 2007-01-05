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
  val add_pretty_imperative_monad_bind: string -> string -> theory -> theory;

  type serializer;
  val add_serializer : string * serializer -> theory -> theory;
  val get_serializer: theory -> string -> Args.T list
    -> string list option -> CodegenThingol.code -> unit;
  val assert_serializer: theory -> string -> string;

  val const_has_serialization: theory -> string list -> string -> bool;
  val tyco_has_serialization: theory -> string list -> string -> bool;

  val eval_verbose: bool ref;
  val eval_term: theory -> CodegenThingol.code
    -> (string * 'a option ref) * CodegenThingol.iterm -> 'a;
  val code_width: int ref;
end;

structure CodegenSerializer: CODEGEN_SERIALIZER =
struct

open BasicCodegenThingol;
val tracing = CodegenThingol.tracing;

(** basics **)

infixr 5 @@;
infixr 5 @|;
fun x @@ y = [x, y];
fun xs @| y = xs @ [y];
val str = setmp print_mode [] Pretty.str;
val concat = Pretty.block o Pretty.breaks;
fun semicolon ps = Pretty.block [concat ps, str ";"];

(** syntax **)

datatype lrx = L | R | X;

datatype fixity =
    BR
  | NOBR
  | INFX of (int * lrx);

val APP = INFX (~1, L);

type 'a pretty_syntax = int * (fixity -> (fixity -> 'a -> Pretty.T)
  -> 'a list -> Pretty.T);

fun eval_lrx L L = false
  | eval_lrx R R = false
  | eval_lrx _ _ = true;

fun eval_fxy NOBR NOBR = false
  | eval_fxy BR NOBR = false
  | eval_fxy NOBR BR = false
  | eval_fxy (INFX (pr, lr)) (INFX (pr_ctxt, lr_ctxt)) =
      pr < pr_ctxt
      orelse pr = pr_ctxt
        andalso eval_lrx lr lr_ctxt
      orelse pr_ctxt = ~1
  | eval_fxy _ (INFX _) = false
  | eval_fxy (INFX _) NOBR = false
  | eval_fxy _ _ = true;

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
        in if k = length ts
          then 
            pr fxy from_expr ts
          else if k < length ts
          then case chop k ts of (ts1, ts2) =>
            brackify fxy (pr APP from_expr ts1 :: map (from_expr BR) ts2)
          else from_expr fxy (CodegenThingol.eta_expand app k)
        end;

val first_upper = implode o nth_map 0 Symbol.to_ascii_upper o explode;
val first_lower = implode o nth_map 0 Symbol.to_ascii_lower o explode;


(* user-defined syntax *)

datatype 'a mixfix =
    Arg of fixity
  | Pretty of Pretty.T;

fun mk_mixfix (fixity_this, mfx) =
  let
    fun is_arg (Arg _) = true
      | is_arg _ = false;
    val i = (length o filter is_arg) mfx;
    fun fillin _ [] [] =
          []
      | fillin pr (Arg fxy :: mfx) (a :: args) =
          pr fxy a :: fillin pr mfx args
      | fillin pr (Pretty p :: mfx) args =
          p :: fillin pr mfx args
      | fillin _ [] _ =
          error ("Inconsistent mixfix: too many arguments")
      | fillin _ _ [] =
          error ("Inconsistent mixfix: too less arguments");
  in
    (i, fn fixity_ctxt => fn pr => fn args =>
      gen_brackify (eval_fxy fixity_this fixity_ctxt) (fillin pr mfx args))
  end;

fun parse_infix (x, i) s =
  let
    val l = case x of L => INFX (i, L) | _ => INFX (i, X);
    val r = case x of R => INFX (i, R) | _ => INFX (i, X);
  in
    mk_mixfix (INFX (i, x), [Arg l, (Pretty o Pretty.brk) 1, (Pretty o str) s, (Pretty o Pretty.brk) 1, Arg r])
  end;

fun parse_mixfix s =
  let
    val sym_any = Scan.one Symbol.not_eof;
    val parse = Scan.optional ($$ "!" >> K true) false -- Scan.repeat (
         ($$ "(" -- $$ "_" -- $$ ")" >> K (Arg NOBR))
      || ($$ "_" >> K (Arg BR))
      || ($$ "/" |-- Scan.repeat ($$ " ") >> (Pretty o Pretty.brk o length))
      || (Scan.repeat1
           (   $$ "'" |-- sym_any
            || Scan.unless ($$ "_" || $$ "/" || $$ "(" |-- $$ "_" |-- $$ ")")
                 sym_any) >> (Pretty o str o implode)));
  in case Scan.finite Symbol.stopper parse (Symbol.explode s)
   of ((_, p as [_]), []) => mk_mixfix (NOBR, p)
    | ((b, p as _ :: _ :: _), []) => mk_mixfix (if b then NOBR else BR, p)
    | _ => Scan.!! (the_default ("malformed mixfix annotation: " ^ quote s) o snd) Scan.fail ()
  end;

fun parse_args f args =
  case Scan.read Args.stopper f args
   of SOME x => x
    | NONE => error "bad serializer arguments";


(* module names *)

val dest_name =
  apfst NameSpace.implode o split_last o fst o split_last o NameSpace.explode;

fun mk_modl_name_tab empty_names prefix module_alias code =
  let
    fun nsp_map f = NameSpace.explode #> map f #> NameSpace.implode;
    fun mk_alias name =
     case module_alias name
      of SOME name' => name'
       | NONE => nsp_map (fn name => (the_single o fst)
            (Name.variants [name] empty_names)) name;
    fun mk_prefix name =
      case prefix
       of SOME prefix => NameSpace.append prefix name
        | NONE => name;
    val tab =
      Symtab.empty
      |> Graph.fold ((fn name => Symtab.default (name, (mk_alias #> mk_prefix) name))
           o fst o dest_name o fst)
             code
  in (fn name => (the o Symtab.lookup tab) name) end;


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
    fun pretty fxy pr [t] =
      case implode_list c_nil c_cons t
       of SOME ts => (case implode_string mk_char mk_string ts
           of SOME p => p
            | NONE => Pretty.block [str target_implode, Pretty.brk 1, pr BR t])
        | NONE => Pretty.block [str target_implode, Pretty.brk 1, pr BR t]
  in (1, pretty) end;

fun pretty_list c_nil c_cons mk_list mk_char_string (target_fxy, target_cons) =
  let
    fun default fxy pr t1 t2 =
      brackify_infix (target_fxy, R) fxy [
        pr (INFX (target_fxy, X)) t1,
        str target_cons,
        pr (INFX (target_fxy, R)) t2
      ];
    fun pretty fxy pr [t1, t2] =
      case Option.map (cons t1) (implode_list c_nil c_cons t2)
       of SOME ts =>
            (case mk_char_string
             of SOME (mk_char, mk_string) =>
                  (case implode_string mk_char mk_string ts
                   of SOME p => p
                    | NONE => mk_list (map (pr NOBR) ts))
              | NONE => mk_list (map (pr NOBR) ts))
        | NONE => default fxy pr t1 t2;
  in (2, pretty) end;

fun pretty_imperative_monad_bind c_bind =
  let
    fun pretty fxy pr [t1, (v, ty) `|-> t2] =
          pr fxy (ICase ((t1, ty), ([(IVar v, t2)])))
      | pretty _ _ _ = error "bad arguments for imperative monad bind";
  in (2, pretty) end;



(** SML/OCaml serializer **)

datatype ml_def =
    MLFuns of (string * ((iterm list * iterm) list * typscheme)) list
  | MLDatas of (string * ((vname * sort) list * (string * itype list) list)) list
  | MLClass of string * (class list * (vname * (string * itype) list))
  | MLClassinst of string * ((class * (string * (vname * sort) list))
        * ((class * (string * inst list list)) list
      * (string * iterm) list));

fun pr_sml tyco_syntax const_syntax keyword_vars deresolv is_cons ml_def =
  let
    fun dictvar v = 
      first_upper v ^ "_";
    val label = translate_string (fn "." => "__" | c => c) o NameSpace.qualifier;
    val mk_classop_name = suffix "_" o snd o dest_name;
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
          | pr_inst fxy (Context ((classes, i), (v, k))) =
              pr_lookup (map (pr_proj o label) classes
                @ (if k = 1 then [] else [(pr_proj o string_of_int) (i+1)])
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
      | pr_typ fxy (ITyVar v) =
          str ("'" ^ v);
    fun pr_term vars fxy (IConst c) =
          pr_app vars fxy (c, [])
      | pr_term vars fxy (IVar v) =
          str (CodegenThingol.lookup_var vars v)
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
                    val vars' = CodegenThingol.intro_vars [v] vars;
                  in
                    (concat [str "fn", str (CodegenThingol.lookup_var vars' v), str "=>"], vars')
                  end
              | pr ((v, SOME p), _) vars =
                  let
                    val vars' = CodegenThingol.intro_vars [v] vars;
                    val vs = CodegenThingol.fold_varnames (insert (op =)) p [];
                    val vars'' = CodegenThingol.intro_vars vs vars';
                  in
                    (concat [str "fn", str (CodegenThingol.lookup_var vars' v), str "as",
                      pr_term vars'' NOBR p, str "=>"], vars'')
                  end;
            val (ps', vars') = fold_map pr ps vars;
          in brackify BR (ps' @ [pr_term vars' NOBR t']) end
      | pr_term vars fxy (INum n) =
          brackify BR [(str o IntInf.toString) n, str ":", str "IntInf.int"]
      | pr_term vars _ (IChar c) =
          (str o prefix "#" o quote)
            (let val i = ord c
              in if i < 32 orelse i = 34 orelse i = 92
                then prefix "\\" (string_of_int i)
                else c
              end)
      | pr_term vars fxy (t as ICase (_, [_])) =
          let
            val (ts, t') = CodegenThingol.unfold_let t;
            fun mk ((p, _), t'') vars =
              let
                val vs = CodegenThingol.fold_varnames (insert (op =)) p [];
                val vars' = CodegenThingol.intro_vars vs vars;
              in
                (Pretty.block [
                  concat [
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
                val vars' = CodegenThingol.intro_vars vs vars;
              in
                concat [
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
        (str o deresolv) c
          :: ((map (pr_insts BR) o filter_out null) iss @ map (pr_term vars BR) ts)
    and pr_app vars fxy (app as ((c, (iss, ty)), ts)) =
      mk_app (pr_app' vars) (pr_term vars) const_syntax fxy app;
    fun pr_def (MLFuns (funns as (funn :: funns'))) =
          let
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
                      |> CodegenThingol.intro_vars consts
                      |> CodegenThingol.intro_vars ((fold o CodegenThingol.fold_unbound_varnames)
                           (insert (op =)) ts []);
                  in
                    concat (
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
                  concat [
                    str (deresolv co),
                    str "of",
                    Pretty.enum " *" "" "" (map (pr_typ (INFX (2, X))) tys)
                  ];
            fun pr_data definer (tyco, (vs, cos)) =
              concat (
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
              (concat o map str) [
                label class, ":", "'" ^ v, deresolv class
              ];
            fun pr_classop (classop, ty) =
              concat [
                (*FIXME?*)
                (str o mk_classop_name) classop, str ":", pr_typ NOBR ty
              ];
            fun pr_classop_fun (classop, _) =
              concat [
                str "fun",
                (str o deresolv) classop,
                Pretty.enclose "(" ")" [str (w ^ ":'" ^ v ^ " " ^ deresolv class)],
                str "=",
                str ("#" ^ mk_classop_name classop),
                str (w ^ ";")
              ];
          in
            Pretty.chunks (
              concat [
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
              concat [
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
                  |> CodegenThingol.intro_vars consts;
              in
                concat [
                  (str o mk_classop_name) classop,
                  str "=",
                  pr_term vars NOBR t
                ]
              end;
          in
            concat ([
              str (if null arity then "val" else "fun"),
              (str o deresolv) inst ] @
              map pr_tyvar arity @ [
              str "=",
              Pretty.enum "," "{" "}" (map pr_superclass superarities @ map pr_classop_def classop_defs),
              str ":",
              pr_tycoexpr NOBR (class, [tyco `%% map (ITyVar o fst) arity]),
              str ";;"
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

fun pr_ocaml tyco_syntax const_syntax keyword_vars deresolv is_cons ml_def =
  let
    fun dictvar v = "_" ^ first_upper v;
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
        fun dot p2 p1 = Pretty.block [p1, str ".", str p2];
        fun proj k i p = (brackify BR o map str) [
            "match",
            p,
            "with",
            replicate i "_" |> nth_map k (K "d") |> separate (", ") |> implode,
            "-> d"
          ]
        fun pr_lookup [] p =
              p
          | pr_lookup [p'] p =
              dot p' p
          | pr_lookup (ps as _ :: _) p =
              fold_rev dot ps p;
        fun pr_inst fxy (Instance (inst, iss)) =
              brackify fxy (
                (str o deresolv) inst
                :: map (pr_insts BR) iss
              )
          | pr_inst fxy (Context ((classes, k), (v, i))) =
              if i = 1 then pr_lookup (map deresolv classes) ((str o dictvar) v)
              else pr_lookup (map deresolv classes) (proj k i (dictvar v));
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
      | pr_typ fxy (ITyVar v) =
          str ("'" ^ v);
    fun pr_term vars fxy (IConst c) =
          pr_app vars fxy (c, [])
      | pr_term vars fxy (IVar v) =
          str (CodegenThingol.lookup_var vars v)
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
                    val vars' = CodegenThingol.intro_vars [v] vars;
                  in
                    (str (CodegenThingol.lookup_var vars' v), vars')
                  end
              | pr ((v, SOME p), _) vars =
                  let
                    val vars' = CodegenThingol.intro_vars [v] vars;
                    val vs = CodegenThingol.fold_varnames (insert (op =)) p [];
                    val vars'' = CodegenThingol.intro_vars vs vars';
                  in
                    (brackify BR [
                        pr_term vars'' NOBR p,
                        str "as",
                        str (CodegenThingol.lookup_var vars' v)
                    ], vars'')
                  end;
            val (ps', vars') = fold_map pr ps vars;
          in brackify BR (
              str "fun"
              :: ps'
              @ str "->"
              @@ pr_term vars' NOBR t'
            )
          end
      | pr_term vars fxy (INum n) =
          brackify BR [str "Big_int.big_int_of_int", (str o IntInf.toString) n]
      | pr_term vars _ (IChar c) =
          (str o enclose "'" "'")
            (let val i = ord c
              in if i < 32 orelse i = 39 orelse i = 92
                then prefix "\\" (string_of_int i)
                else c
              end)
      | pr_term vars fxy (t as ICase (_, [_])) =
          let
            val (ts, t') = CodegenThingol.unfold_let t;
            fun mk ((p, _), t'') vars =
              let
                val vs = CodegenThingol.fold_varnames (insert (op =)) p [];
                val vars' = CodegenThingol.intro_vars vs vars;
              in
                (concat [
                  str "let",
                  pr_term vars' NOBR p,
                  str "=",
                  pr_term vars NOBR t'',
                  str "in"
                ], vars')
              end
            val (binds, vars') = fold_map mk ts vars;
          in
            Pretty.chunks (binds @ [pr_term vars' NOBR t'])
          end
      | pr_term vars fxy (ICase ((td, ty), b::bs)) =
          let
            fun pr definer (p, t) =
              let
                val vs = CodegenThingol.fold_varnames (insert (op =)) p [];
                val vars' = CodegenThingol.intro_vars vs vars;
              in
                concat [
                  str definer,
                  pr_term vars' NOBR p,
                  str "->",
                  pr_term vars' NOBR t
                ]
              end;
          in
            (Pretty.enclose "(" ")" o single o brackify fxy) (
              str "match"
              :: pr_term vars NOBR td
              :: pr "with" b
              :: map (pr "|") bs
            )
          end
    and pr_app' vars (app as ((c, (iss, ty)), ts)) =
      if is_cons c then
        if (length o fst o CodegenThingol.unfold_fun) ty = length ts
        then case ts
         of [] => [(str o deresolv) c]
          | [t] => [(str o deresolv) c, pr_term vars BR t]
          | _ => [(str o deresolv) c, Pretty.enum "," "(" ")" (map (pr_term vars NOBR) ts)]
        else [pr_term vars BR (CodegenThingol.eta_expand app ((length o fst o CodegenThingol.unfold_fun) ty))]
      else (str o deresolv) c
        :: ((map (pr_insts BR) o filter_out null) iss @ map (pr_term vars BR) ts)
    and pr_app vars fxy (app as ((c, (iss, ty)), ts)) =
      mk_app (pr_app' vars) (pr_term vars) const_syntax fxy app;
    fun pr_def (MLFuns (funns as funn :: funns')) =
          let
            fun fish_parm _ (w as SOME _) = w
              | fish_parm (IVar v) NONE = SOME v
              | fish_parm _ NONE = NONE;
            fun fillup_parm _ (_, SOME v) = v
              | fillup_parm x (i, NONE) = x ^ string_of_int i;
            fun fish_parms vars eqs =
              let
                val raw_fished = fold (map2 fish_parm) eqs (replicate (length (hd eqs)) NONE);
                val x = Name.variant (map_filter I raw_fished) "x";
                val fished = map_index (fillup_parm x) raw_fished;
                val vars' = CodegenThingol.intro_vars fished vars;
              in map (CodegenThingol.lookup_var vars') fished end;
            fun pr_eq (ts, t) =
              let
                val consts = map_filter
                  (fn c => if (is_some o const_syntax) c
                    then NONE else (SOME o NameSpace.base o deresolv) c)
                    ((fold o CodegenThingol.fold_constnames) (insert (op =)) (t :: ts) []);
                val vars = keyword_vars
                  |> CodegenThingol.intro_vars consts
                  |> CodegenThingol.intro_vars ((fold o CodegenThingol.fold_unbound_varnames)
                      (insert (op =)) ts []);
              in concat [
                (Pretty.block o Pretty.commas) (map (pr_term vars NOBR) ts),
                str "->",
                pr_term vars NOBR t
              ] end;
            fun pr_eqs [(ts, t)] =
                  let
                    val consts = map_filter
                      (fn c => if (is_some o const_syntax) c
                        then NONE else (SOME o NameSpace.base o deresolv) c)
                        ((fold o CodegenThingol.fold_constnames) (insert (op =)) (t :: ts) []);
                    val vars = keyword_vars
                      |> CodegenThingol.intro_vars consts
                      |> CodegenThingol.intro_vars ((fold o CodegenThingol.fold_unbound_varnames)
                          (insert (op =)) ts []);
                  in
                    concat (
                      map (pr_term vars BR) ts
                      @ str "="
                      @@ pr_term vars NOBR t
                    )
                  end
              | pr_eqs (eqs as (eq as ([_], _)) :: eqs') =
                  Pretty.block (
                    str "="
                    :: Pretty.brk 1
                    :: str "function"
                    :: Pretty.brk 1
                    :: pr_eq eq
                    :: maps (append [Pretty.fbrk, str "|", Pretty.brk 1] o single o pr_eq) eqs'
                  )
              | pr_eqs (eqs as eq :: eqs') =
                  let
                    val consts = map_filter
                      (fn c => if (is_some o const_syntax) c
                        then NONE else (SOME o NameSpace.base o deresolv) c)
                        ((fold o CodegenThingol.fold_constnames) (insert (op =)) (map snd eqs) []);
                    val vars = keyword_vars
                      |> CodegenThingol.intro_vars consts;
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
                      :: maps (append [Pretty.fbrk, str "|", Pretty.brk 1] o single o pr_eq) eqs'
                    )
                  end;
            fun pr_funn definer (name, (eqs, (vs, ty))) =
              concat (
                str definer
                :: (str o deresolv) name
                :: map_filter (fn (_, []) => NONE | v => SOME (pr_tyvar v)) vs
                @| pr_eqs eqs
              );
            val (ps, p) = split_last (pr_funn "let rec" funn :: map (pr_funn "and") funns');
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
            fun pr_data definer (tyco, (vs, cos)) =
              concat (
                str definer
                :: pr_tycoexpr NOBR (tyco, map (ITyVar o fst) vs)
                :: str "="
                :: separate (str "|") (map pr_co cos)
              );
            val (ps, p) = split_last (pr_data "type" data :: map (pr_data "and") datas');
          in Pretty.chunks (ps @ [Pretty.block ([p, str ";;"])]) end
     | pr_def (MLClass (class, (superclasses, (v, classops)))) =
          let
            val w = dictvar v;
            fun pr_superclass class =
              (concat o map str) [
                deresolv class, ":", "'" ^ v, deresolv class
              ];
            fun pr_classop (classop, ty) =
              concat [
                (str o deresolv) classop, str ":", pr_typ NOBR ty
              ];
            fun pr_classop_fun (classop, _) =
              concat [
                str "let",
                (str o deresolv) classop,
                Pretty.enclose "(" ")" [str (w ^ ":'" ^ v ^ " " ^ deresolv class)],
                str "=",
                str (w ^ "." ^ deresolv classop ^ ";;")
              ];
          in
            Pretty.chunks (
              concat [
                str ("type '" ^ v),
                (str o deresolv) class,
                str "=",
                Pretty.enum ";" "{" "};;" (
                  map pr_superclass superclasses @ map pr_classop classops
                )
              ]
              :: map pr_classop_fun classops
            )
          end
     | pr_def (MLClassinst (inst, ((class, (tyco, arity)), (superarities, classop_defs)))) =
          let
            fun pr_superclass (superclass, superinst_iss) =
              concat [
                (str o deresolv) superclass,
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
                  |> CodegenThingol.intro_vars consts;
              in
                concat [
                  (str o deresolv) classop,
                  str "=",
                  pr_term vars NOBR t
                ]
              end;
          in
            concat (
              str "let"
              :: (str o deresolv) inst
              :: map pr_tyvar arity
              @ str "="
              @@ (Pretty.enclose "(" ");;" o Pretty.breaks) [
                Pretty.enum ";" "{" "}" (map pr_superclass superarities @ map pr_classop_def classop_defs),
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

val code_width = ref 80;
fun code_output p = Pretty.setmp_margin (!code_width) Pretty.output p ^ "\n";

fun seri_ml pr_def pr_modl output reserved_user module_alias module_prolog
  (_ : string -> (string * (string -> string option)) option) tyco_syntax const_syntax code =
  let
    val is_cons = fn node => case CodegenThingol.get_def code node
     of CodegenThingol.Datatypecons _ => true
      | _ => false;
    datatype node =
        Def of string * ml_def option
      | Module of string * ((Name.context * Name.context) * node Graph.T);
    val empty_names = ML_Syntax.reserved |> fold Name.declare reserved_user;
    val empty_module = ((empty_names, empty_names), Graph.empty);
    fun map_node [] f = f
      | map_node (m::ms) f =
          Graph.default_node (m, Module (m, empty_module))
          #> Graph.map_node m (fn (Module (dmodlname, (nsp, nodes))) => Module (dmodlname, (nsp, map_node ms f nodes)));
    fun map_nsp_yield [] f (nsp, nodes) =
          let
            val (x, nsp') = f nsp
          in (x, (nsp', nodes)) end
      | map_nsp_yield (m::ms) f (nsp, nodes) =
          let
            val (x, nodes') =
              nodes
              |> Graph.default_node (m, Module (m, empty_module))
              |> Graph.map_node_yield m (fn Module (dmodlname, nsp_nodes) => 
                  let
                    val (x, nsp_nodes') = map_nsp_yield ms f nsp_nodes
                  in (x, Module (dmodlname, nsp_nodes')) end)
          in (x, (nsp, nodes')) end;
    val init_vars = CodegenThingol.make_vars (ML_Syntax.reserved_names @ reserved_user);
    val name_modl = mk_modl_name_tab empty_names NONE module_alias code;
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
        (fn (name, CodegenThingol.Fun info) =>
              map_nsp_fun (name_def false name) >> (fn base => (base, (name, info)))
          | (name, def) => error ("Function block containing illegal def: " ^ quote name)
        ) defs
      >> (split_list #> apsnd MLFuns);
    fun mk_datatype defs =
      fold_map
        (fn (name, CodegenThingol.Datatype info) =>
              map_nsp_typ (name_def false name) >> (fn base => (base, SOME (name, info)))
          | (name, CodegenThingol.Datatypecons _) =>
              map_nsp_fun (name_def true name) >> (fn base => (base, NONE))
          | (name, def) => error ("Datatype block containing illegal def: " ^ quote name)
        ) defs
      >> (split_list #> apsnd (map_filter I
        #> (fn [] => error ("Datatype block without data: " ^ (commas o map (quote o fst)) defs)
             | infos => MLDatas infos)));
    fun mk_class defs =
      fold_map
        (fn (name, CodegenThingol.Class info) =>
              map_nsp_typ (name_def false name) >> (fn base => (base, SOME (name, info)))
          | (name, CodegenThingol.Classop _) =>
              map_nsp_fun (name_def false name) >> (fn base => (base, NONE))
          | (name, def) => error ("Class block containing illegal def: " ^ quote name)
        ) defs
      >> (split_list #> apsnd (map_filter I
        #> (fn [] => error ("Class block without class: " ^ (commas o map (quote o fst)) defs)
             | [info] => MLClass info)));
    fun mk_inst [(name, CodegenThingol.Classinst info)] =
      map_nsp_fun (name_def false name)
      >> (fn base => ([base], MLClassinst (name, info)));
    fun add_group mk defs nsp_nodes =
      let
        val names as (name :: names') = map fst defs;
        val deps =
          []
          |> fold (fold (insert (op =)) o Graph.imm_succs code) names
          |> subtract (op =) names;
        val (modls, _) = (split_list o map dest_name) names;
        val modl = (the_single o distinct (op =)) modls
          handle Empty =>
            error ("Illegal mutual dependencies: " ^ commas names);
        val modl' = name_modl modl;
        val modl_explode = NameSpace.explode modl';
        fun add_dep name name'' =
          let
            val modl'' = (name_modl o fst o dest_name) name'';
          in if modl' = modl'' then
            map_node modl_explode
              (Graph.add_edge (name, name''))
          else let
            val (common, (diff1::_, diff2::_)) = chop_prefix (op =) (modl_explode, NameSpace.explode modl'');
          in
            map_node common
              (fn gr => Graph.add_edge_acyclic (diff1, diff2) gr
                handle Graph.CYCLES _ => error ("Dependency "
                  ^ quote name
                  ^ " -> " ^ quote name'' ^ " would result in module dependency cycle"))
          end end;
      in
        nsp_nodes
        |> map_nsp_yield modl_explode (mk defs)
        |-> (fn (base' :: bases', def') =>
           apsnd (map_node modl_explode (Graph.new_node (name, (Def (base', SOME def')))
              #> fold2 (fn name' => fn base' => Graph.new_node (name', (Def (base', NONE)))) names' bases')))
        |> apsnd (fold (fn name => fold (add_dep name) deps) names)
        |> apsnd (fold (map_node modl_explode o Graph.add_edge) (product names names))
      end;
    fun group_defs [(_, CodegenThingol.Bot)] =
          I
      | group_defs ((defs as (_, CodegenThingol.Fun _)::_)) =
          add_group mk_funs defs
      | group_defs ((defs as (_, CodegenThingol.Datatypecons _)::_)) =
          add_group mk_datatype defs
      | group_defs ((defs as (_, CodegenThingol.Datatype _)::_)) =
          add_group mk_datatype defs
      | group_defs ((defs as (_, CodegenThingol.Class _)::_)) =
          add_group mk_class defs
      | group_defs ((defs as (_, CodegenThingol.Classop _)::_)) =
          add_group mk_class defs
      | group_defs ((defs as [(_, CodegenThingol.Classinst _)])) =
          add_group mk_inst defs
      | group_defs defs = error ("Illegal mutual dependencies: " ^ (commas o map fst) defs)
    val (_, nodes) =
      empty_module
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
      in NameSpace.implode (remainder @ [defname']) end handle Graph.UNDEF _ =>
        "(raise Fail \"undefined name " ^ name ^ "\")";
    fun the_prolog modlname = case module_prolog modlname
     of NONE => []
      | SOME p => [p, str ""];
    fun pr_node prefix (Def (_, NONE)) =
          NONE
      | pr_node prefix (Def (_, SOME def)) =
          SOME (pr_def tyco_syntax const_syntax init_vars (deresolver prefix) is_cons def)
      | pr_node prefix (Module (dmodlname, (_, nodes))) =
          SOME (pr_modl dmodlname (the_prolog (NameSpace.implode (prefix @ [dmodlname]))
            @ separate (str "") ((map_filter (pr_node (prefix @ [dmodlname]) o Graph.get_node nodes)
                o rev o flat o Graph.strong_conn) nodes)));
    val p = pr_modl "ROOT" (the_prolog "" @ separate (str "") ((map_filter
      (pr_node [] o Graph.get_node nodes) o rev o flat o Graph.strong_conn) nodes))
  in output p end;

val isar_seri_sml =
  let
    fun output_file file = File.write (Path.explode file) o code_output;
    val output_diag = writeln o code_output;
    val output_internal = use_text Output.ml_output false o code_output;
  in
    parse_args ((Args.$$$ "-" >> K output_diag
      || Args.$$$ "#" >> K output_internal
      || Args.name >> output_file)
    >> (fn output => seri_ml pr_sml pr_sml_modl output))
  end;

val isar_seri_ocaml =
  let
    fun output_file file = File.write (Path.explode file) o code_output;
    val output_diag = writeln o code_output;
  in
    parse_args ((Args.$$$ "-" >> K output_diag
      || Args.name >> output_file)
    >> (fn output => seri_ml pr_ocaml pr_ocaml_modl output))
  end;


(** Haskell serializer **)

fun pr_haskell class_syntax tyco_syntax const_syntax keyword_vars deresolv_here deresolv deriving_show def =
  let
    fun class_name class = case class_syntax class
     of NONE => deresolv class
      | SOME (class, _) => class;
    fun classop_name class classop = case class_syntax class
     of NONE => deresolv_here classop
      | SOME (_, classop_syntax) => case classop_syntax classop
         of NONE => (snd o dest_name) classop
          | SOME classop => classop
    fun pr_typparms tyvars vs =
      case maps (fn (v, sort) => map (pair v) sort) vs
       of [] => str ""
        | xs => Pretty.block [
            Pretty.enum "," "(" ")" (
              map (fn (v, class) => str
                (class_name class ^ " " ^ CodegenThingol.lookup_var tyvars v)) xs
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
      | pr_typ tyvars fxy (ITyVar v) =
          (str o CodegenThingol.lookup_var tyvars) v;
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
          (str o CodegenThingol.lookup_var vars) v
      | pr_term vars fxy (t as _ `|-> _) =
          let
            val (ps, t') = CodegenThingol.unfold_abs t;
            fun pr ((v, SOME p), _) vars =
                  let
                    val vars' = CodegenThingol.intro_vars [v] vars;
                    val vs = CodegenThingol.fold_varnames (insert (op =)) p [];
                    val vars'' = CodegenThingol.intro_vars vs vars';
                  in
                    (concat [str (CodegenThingol.lookup_var vars' v),
                      str "@", pr_term vars'' BR p], vars'')
                  end
              | pr ((v, NONE), _) vars =
                  let
                    val vars' = CodegenThingol.intro_vars [v] vars;
                  in (str (CodegenThingol.lookup_var vars' v), vars') end;
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
              in if i < 32 orelse i = 39 orelse i = 92
                then Library.prefix "\\" (string_of_int i)
                else c
              end)
      | pr_term vars fxy (t as ICase (_, [_])) =
          let
            val (ts, t) = CodegenThingol.unfold_let t;
            fun pr ((p, _), t) vars =
              let
                val vs = CodegenThingol.fold_varnames (insert (op =)) p [];
                val vars' = CodegenThingol.intro_vars vs vars;
              in
                (semicolon [
                  pr_term vars' BR p,
                  str "=",
                  pr_term vars NOBR t
                ], vars')
              end;
            val (binds, vars') = fold_map pr ts vars;
          in
            Pretty.block_enclose (
              str "let {",
              Pretty.block [str "} in ", pr_term vars' NOBR t]
            ) binds
          end
      | pr_term vars fxy (ICase ((td, _), bs)) =
          let
            fun pr (p, t) =
              let
                val vs = CodegenThingol.fold_varnames (insert (op =)) p [];
                val vars' = CodegenThingol.intro_vars vs vars;
              in
                semicolon [
                  pr_term vars' NOBR p,
                  str "->",
                  pr_term vars' NOBR t
                ]
              end
          in
            Pretty.block_enclose (
              concat [str "(case", pr_term vars NOBR td, str "of", str "{"],
              str "})"
            ) (map pr bs)
          end
    and pr_app' vars ((c, _), ts) =
      (str o deresolv) c :: map (pr_term vars BR) ts
    and pr_app vars fxy =
      mk_app (pr_app' vars) (pr_term vars) const_syntax fxy;
    fun pr_def (name, CodegenThingol.Fun (eqs, (vs, ty))) =
          let
            val tyvars = CodegenThingol.intro_vars (map fst vs) keyword_vars;
            fun pr_eq (ts, t) =
              let
                val consts = map_filter
                  (fn c => if (is_some o const_syntax) c
                    then NONE else (SOME o NameSpace.base o deresolv) c)
                    ((fold o CodegenThingol.fold_constnames) (insert (op =)) (t :: ts) []);
                val vars = keyword_vars
                  |> CodegenThingol.intro_vars consts
                  |> CodegenThingol.intro_vars ((fold o CodegenThingol.fold_unbound_varnames)
                       (insert (op =)) ts []);
              in
                semicolon (
                  (str o deresolv_here) name
                  :: map (pr_term vars BR) ts
                  @ str "="
                  @@ pr_term vars NOBR t
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
      | pr_def (name, CodegenThingol.Datatype (vs, [(co, [ty])])) =
          let
            val tyvars = CodegenThingol.intro_vars (map fst vs) keyword_vars;
          in
            semicolon (
              str "newtype"
              :: pr_typscheme_expr tyvars (vs, (deresolv_here name, map (ITyVar o fst) vs))
              :: str "="
              :: (str o deresolv_here) co
              :: pr_typ tyvars BR ty
              :: (if deriving_show name then [str "deriving (Read, Show)"] else [])
            )
          end
      | pr_def (name, CodegenThingol.Datatype (vs, co :: cos)) =
          let
            val tyvars = CodegenThingol.intro_vars (map fst vs) keyword_vars;
            fun pr_co (co, tys) =
              concat (
                (str o deresolv_here) co
                :: map (pr_typ tyvars BR) tys
              )
          in
            semicolon (
              str "data"
              :: pr_typscheme_expr tyvars (vs, (deresolv_here name, map (ITyVar o fst) vs))
              :: str "="
              :: pr_co co
              :: map ((fn p => Pretty.block [str "| ", p]) o pr_co) cos
              @ (if deriving_show name then [str "deriving (Read, Show)"] else [])
            )
          end
      | pr_def (name, CodegenThingol.Class (superclasss, (v, classops))) =
          let
            val tyvars = CodegenThingol.intro_vars [v] keyword_vars;
            fun pr_classop (classop, ty) =
              semicolon [
                (str o classop_name name) classop,
                str "::",
                pr_typ tyvars NOBR ty
              ]
          in
            Pretty.block_enclose (
              Pretty.block [
                str "class ",
                pr_typparms tyvars [(v, superclasss)],
                str (deresolv_here name ^ " " ^ CodegenThingol.lookup_var tyvars v),
                str " where {"
              ],
              str "};"
            ) (map pr_classop classops)
          end
      | pr_def (_, CodegenThingol.Classinst ((class, (tyco, vs)), (_, classop_defs))) =
          let
            val tyvars = CodegenThingol.intro_vars (map fst vs) keyword_vars;
            fun pr_instdef (classop, t) =
                let
                  val consts = map_filter
                    (fn c => if (is_some o const_syntax) c
                      then NONE else (SOME o NameSpace.base o deresolv) c)
                      (CodegenThingol.fold_constnames (insert (op =)) t []);
                  val vars = keyword_vars
                    |> CodegenThingol.intro_vars consts;
                in
                  semicolon [
                    (str o classop_name class) classop,
                    str "=",
                    pr_term vars NOBR t
                  ]
                end;
          in
            Pretty.block_enclose (
              Pretty.block [
                str "instance ",
                pr_typparms tyvars vs,
                str (class_name class ^ " "),
                pr_typ tyvars BR (tyco `%% map (ITyVar o fst) vs),
                str " where {"
              ],
              str "};"
            ) (map pr_instdef classop_defs)
          end;
  in pr_def def end;

val reserved_haskell = [
  "hiding", "deriving", "where", "case", "of", "infix", "infixl", "infixr",
  "import", "default", "forall", "let", "in", "class", "qualified", "data",
  "newtype", "instance", "if", "then", "else", "type", "as", "do", "module"
];

fun seri_haskell module_prefix destination string_classes reserved_user module_alias module_prolog
  class_syntax tyco_syntax const_syntax code =
  let
    val _ = Option.map File.check destination;
    val empty_names = Name.make_context (reserved_haskell @ reserved_user);
    val name_modl = mk_modl_name_tab empty_names module_prefix module_alias code
    fun add_def (name, (def, deps : string list)) =
      let
        val (modl, base) = dest_name name;
        fun name_def base = Name.variants [base] #>> the_single;
        fun add_fun upper (nsp_fun, nsp_typ) =
          let
            val (base', nsp_fun') = name_def (if upper then first_upper base else base) nsp_fun
          in (base', (nsp_fun', nsp_typ)) end;
        fun add_typ (nsp_fun, nsp_typ) =
          let
            val (base', nsp_typ') = name_def (first_upper base) nsp_typ
          in (base', (nsp_fun, nsp_typ')) end;
        val add_name =
          case def
           of CodegenThingol.Bot => pair base
            | CodegenThingol.Fun _ => add_fun false
            | CodegenThingol.Datatype _ => add_typ
            | CodegenThingol.Datatypecons _ => add_fun true
            | CodegenThingol.Class _ => add_typ
            | CodegenThingol.Classop _ => add_fun false
            | CodegenThingol.Classinst _ => pair base;
        val modlname' = name_modl modl;
        fun add_def base' =
          case def
           of CodegenThingol.Bot => I
            | CodegenThingol.Datatypecons _ => I
                cons (name, ((NameSpace.append modlname' base', base'), NONE))
            | CodegenThingol.Classop _ =>
                cons (name, ((NameSpace.append modlname' base', base'), NONE))
            | _ => cons (name, ((NameSpace.append modlname' base', base'), SOME def));
      in
        Symtab.map_default (modlname', ([], ([], (empty_names, empty_names))))
              (apfst (fold (insert (op =)) deps))
        #> `(fn code => add_name ((snd o snd o the o Symtab.lookup code) modlname'))
        #-> (fn (base', names) =>
              (Symtab.map_entry modlname' o apsnd) (fn (defs, _) =>
              (add_def base' defs, names)))
      end;
    val code' =
      fold add_def (AList.make (fn name => (Graph.get_node code name, Graph.imm_succs code name))
        (Graph.strong_conn code |> flat)) Symtab.empty;
    val init_vars = CodegenThingol.make_vars (reserved_haskell @ reserved_user);
    fun deresolv name =
      (fst o fst o the o AList.lookup (op =) ((fst o snd o the
        o Symtab.lookup code') ((name_modl o fst o dest_name) name))) name
        handle Option => "(error \"undefined name " ^ name ^ "\")";
    fun deresolv_here name =
      (snd o fst o the o AList.lookup (op =) ((fst o snd o the
        o Symtab.lookup code') ((name_modl o fst o dest_name) name))) name
        handle Option => "(error \"undefined name " ^ name ^ "\")";
    fun deriving_show tyco =
      let
        fun deriv _ "fun" = false
          | deriv tycos tyco = member (op =) tycos tyco orelse
              case the_default CodegenThingol.Bot (try (Graph.get_node code) tyco)
               of CodegenThingol.Bot => true
                | CodegenThingol.Datatype (_, cs) => forall (deriv' (tyco :: tycos))
                    (maps snd cs)
        and deriv' tycos (tyco `%% tys) = deriv tycos tyco
              andalso forall (deriv' tycos) tys
          | deriv' _ (ITyVar _) = true
      in deriv [] tyco end;
    fun seri_def qualified = pr_haskell class_syntax tyco_syntax const_syntax init_vars
      deresolv_here (if qualified then deresolv else deresolv_here) (if string_classes then deriving_show else K false);
    fun write_module (SOME destination) modlname =
          let
            val filename = case modlname
             of "" => Path.explode "Main.hs"
              | _ => (Path.ext "hs" o Path.explode o implode o separate "/" o NameSpace.explode) modlname;
            val pathname = Path.append destination filename;
            val _ = File.mkdir (Path.dir pathname);
          in File.write pathname end
      | write_module NONE _ = writeln;
    fun seri_module (modlname', (imports, (defs, _))) =
      let
        val imports' =
          imports
          |> map (name_modl o fst o dest_name)
          |> distinct (op =)
          |> remove (op =) modlname';
        val qualified =
          imports
          |> map_filter (try deresolv)
          |> map NameSpace.base
          |> has_duplicates (op =);
        val mk_import = str o (if qualified
          then prefix "import qualified "
          else prefix "import ") o suffix ";";
      in
        Pretty.chunks (
          str ("module " ^ modlname' ^ " where {")
          :: str ""
          :: map mk_import imports'
          @ str ""
          :: separate (str "") ((case module_prolog modlname'
             of SOME prolog => [prolog]
              | NONE => [])
          @ map_filter
            (fn (name, (_, SOME def)) => SOME (seri_def qualified (name, def))
              | (_, (_, NONE)) => NONE) defs)
          @ str ""
          @@ str "}"
        )
        |> code_output
        |> write_module destination modlname'
      end;
  in Symtab.fold (fn modl => fn () => seri_module modl) code' () end;

val isar_seri_haskell =
  parse_args (Scan.option (Args.$$$ "root" -- Args.colon |-- Args.name)
    -- Scan.optional (Args.$$$ "string_classes" >> K true) false
    -- (Args.$$$ "-" >> K NONE || Args.name >> SOME)
    >> (fn ((module_prefix, string_classes), destination) =>
      seri_haskell module_prefix (Option.map Path.explode destination) string_classes));


(** diagnosis serializer **)

fun seri_diagnosis _ _ _ _ _ code =
  let
    val init_vars = CodegenThingol.make_vars reserved_haskell;
    val pr = pr_haskell (K NONE) (K NONE) (K NONE) init_vars I I (K false);
  in
    []
    |> Graph.fold (fn (name, (def, _)) => case try pr (name, def) of SOME p => cons p | NONE => I) code
    |> Pretty.chunks2
    |> code_output
    |> writeln
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
  #> add_serializer ("SML", isar_seri_sml)
  #> add_serializer ("OCaml", isar_seri_ocaml)
  #> add_serializer ("Haskell", isar_seri_haskell)
  #> add_serializer (target_diag, (fn _ => fn _ => seri_diagnosis))
);

fun get_serializer thy target args = fn cs =>
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

val eval_verbose = ref false;

fun eval_term thy code ((ref_name, reff), t) =
  let
    val val_name = "eval.EVAL.EVAL";
    val val_name' = "ROOT.eval.EVAL";
    val data = (the o Symtab.lookup (CodegenSerializerData.get thy)) "SML"
    val reserved = the_reserved data;
    val { alias, prolog } = the_syntax_modl data;
    val { class, inst, tyco, const } = the_syntax_expr data;
    fun fun_of sys = (Option.map fst oo Symtab.lookup) sys;
    fun eval p = (
      reff := NONE;
      if !eval_verbose then Pretty.writeln p else ();
      use_text Output.ml_output (!eval_verbose)
        ((Pretty.output o Pretty.chunks) [p,
          str ("val _ = (" ^ ref_name ^ " := SOME " ^ val_name' ^ ")")
        ]);
      case !reff
       of NONE => error ("Could not retrieve value of ML reference " ^ quote ref_name
            ^ " (reference probably has been shadowed)")
        | SOME value => value
      );
  in
    code
    |> CodegenThingol.add_eval_def (val_name, t)
    |> CodegenThingol.project_code
        (Symtab.keys class @ Symtab.keys inst @ Symtab.keys tyco @ Symtab.keys const)
          (SOME [val_name])
    |> seri_ml pr_sml pr_sml_modl I reserved (Symtab.lookup alias) (Symtab.lookup prolog)
        (fun_of class) (fun_of tyco) (fun_of const)
    |> eval
  end;

fun assert_serializer thy target =
  case Symtab.lookup (CodegenSerializerData.get thy) target
   of SOME data => target
    | NONE => error ("Unknown code target language: " ^ quote target);

fun has_serialization f thy targets name =
  forall (
    is_some o (fn tab => Symtab.lookup tab name) o f o the_syntax_expr o the
      o Symtab.lookup (CodegenSerializerData.get thy)
  ) targets;

val tyco_has_serialization = has_serialization #tyco;
val const_has_serialization = has_serialization #const;



(** ML and toplevel interface **)

local

fun map_syntax_exprs target =
  map_seri_data target o (apsnd o apsnd o apfst o map_syntax_expr);
fun map_syntax_modls target =
  map_seri_data target o (apsnd o apsnd o apsnd o map_syntax_modl);
fun map_reserveds target =
  map_seri_data target o (apsnd o apfst o apsnd);

fun gen_add_syntax_class prep_class prep_const target raw_class raw_syn thy =
  let
    val cls = prep_class thy raw_class;
    val class = CodegenNames.class thy cls;
    fun mk_classop (const as (c, _)) = case AxClass.class_of_param thy c
     of SOME class' => if cls = class' then CodegenNames.const thy const
          else error ("Not a class operation for class " ^ quote class ^ ": " ^ quote c)
      | NONE => error ("Not a class operation: " ^ quote c);
    fun mk_syntax_ops raw_ops = AList.lookup (op =)
      ((map o apfst) (mk_classop o prep_const thy) raw_ops);
  in case raw_syn
   of SOME (syntax, raw_ops) =>
      thy
      |> (map_syntax_exprs target o apfst o apfst)
           (Symtab.update (class, ((syntax, mk_syntax_ops raw_ops), serial ())))
    | NONE =>
      thy
      |> (map_syntax_exprs target o apfst o apfst)
           (Symtab.delete_safe class)
  end;

fun gen_add_syntax_inst prep_class prep_tyco target (raw_tyco, raw_class) add_del thy =
  let
    val inst = CodegenNames.instance thy (prep_class thy raw_class, prep_tyco thy raw_tyco);
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
    val tyco' = if tyco = "fun" then "fun" else CodegenNames.tyco thy tyco;
    fun check_args (syntax as (n, _)) = if n <> Sign.arity_number thy tyco
      then error ("Number of arguments mismatch in syntax for type constructor " ^ quote tyco)
      else syntax
  in case raw_syn
   of SOME syntax =>
      thy
      |> (map_syntax_exprs target o apsnd o apfst)
           (Symtab.update (tyco', (check_args syntax, serial ())))
   | NONE =>
      thy
      |> (map_syntax_exprs target o apsnd o apfst)
           (Symtab.delete_safe tyco')
  end;

fun gen_add_syntax_const prep_const target raw_c raw_syn thy =
  let
    val c = prep_const thy raw_c;
    val c' = CodegenNames.const thy c;
    fun check_args (syntax as (n, _)) = if n > (length o fst o strip_type o Sign.the_const_type thy o fst) c
      then error ("Too many arguments in syntax for constant " ^ (quote o fst) c)
      else syntax;
  in case raw_syn
   of SOME syntax =>
      thy
      |> (map_syntax_exprs target o apsnd o apsnd)
           (Symtab.update (c', (check_args syntax, serial ())))
   | NONE =>
      thy
      |> (map_syntax_exprs target o apsnd o apsnd)
           (Symtab.delete_safe c')
  end;

(*fun gen_add_syntax_monad prep_tyco target raw_tyco monad_tyco thy =
  let
    val _ = if 
  in
    thy
  end;*)

fun read_class thy raw_class =
  let
    val class = Sign.intern_class thy raw_class;
    val _ = AxClass.get_definition thy class;
  in class end;

fun read_type thy raw_tyco =
  let
    val tyco = Sign.intern_type thy raw_tyco;
    val _ = if Sign.declared_tyname thy tyco then ()
      else error ("No such type constructor: " ^ quote raw_tyco);
  in tyco end;

fun idfs_of_const_names thy c =
  let
    val c' = (c, Sign.the_const_type thy c);
    val c'' = CodegenConsts.norm_of_typ thy c';
  in (c'', CodegenNames.const thy c'') end;

val add_syntax_class = gen_add_syntax_class read_class CodegenConsts.read_const;
val add_syntax_inst = gen_add_syntax_inst read_class read_type;
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

val (infixK, infixlK, infixrK) = ("infix", "infixl", "infixr");

fun parse_syntax xs =
  Scan.option ((
      ((P.$$$ infixK  >> K X)
        || (P.$$$ infixlK >> K L)
        || (P.$$$ infixrK >> K R))
        -- P.nat >> parse_infix
      || Scan.succeed parse_mixfix)
      -- P.string
      >> (fn (parse, s) => parse s)) xs;

val (code_classK, code_instanceK, code_typeK, code_constK, code_monadK,
  code_reservedK, code_modulenameK, code_moduleprologK) =
  ("code_class", "code_instance", "code_type", "code_const", "code_monad",
    "code_reserved", "code_modulename", "code_moduleprolog");

in

fun add_pretty_list target nill cons mk_list mk_char_string target_cons thy =
  let
    val (_, nil'') = idfs_of_const_names thy nill;
    val (cons', cons'') = idfs_of_const_names thy cons;
    val pr = pretty_list nil'' cons'' mk_list mk_char_string target_cons;
  in
    thy
    |> gen_add_syntax_const (K I) target cons' (SOME pr)
  end;

fun add_pretty_ml_string target nill cons str mk_char mk_string target_implode thy =
  let
    val (_, nil'') = idfs_of_const_names thy nill;
    val (_, cons'') = idfs_of_const_names thy cons;
    val (str', _) = idfs_of_const_names thy str;
    val pr = pretty_ml_string nil'' cons'' mk_char mk_string target_implode;
  in
    thy
    |> gen_add_syntax_const (K I) target str' (SOME pr)
  end;

fun add_undefined target undef target_undefined thy =
  let
    val (undef', _) = idfs_of_const_names thy undef;
    fun pr _ _ _ = str target_undefined;
  in
    thy
    |> gen_add_syntax_const (K I) target undef' (SOME (~1, pr))
  end;

fun add_pretty_imperative_monad_bind target bind thy =
  let
    val (bind', bind'') = idfs_of_const_names thy bind;
    val pr = pretty_imperative_monad_bind bind''
  in
    thy
    |> gen_add_syntax_const (K I) target bind' (SOME pr)
  end;

val code_classP =
  OuterSyntax.command code_classK "define code syntax for class" K.thy_decl (
    parse_multi_syntax P.xname
      (Scan.option (P.string -- Scan.optional (P.$$$ "where" |-- Scan.repeat1
        (P.term --| (P.$$$ "\\<equiv>" || P.$$$ "==") -- P.string)) []))
    >> (Toplevel.theory oo fold) (fn (target, syns) =>
          fold (fn (raw_class, syn) => add_syntax_class target raw_class syn) syns)
  );

val code_instanceP =
  OuterSyntax.command code_instanceK "define code syntax for instance" K.thy_decl (
    parse_multi_syntax (P.xname --| P.$$$ "::" -- P.xname)
      ((P.minus >> K true) || Scan.succeed false)
    >> (Toplevel.theory oo fold) (fn (target, syns) =>
          fold (fn (raw_inst, add_del) => add_syntax_inst target raw_inst add_del) syns)
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

(*val code_monadP =
  OuterSyntax.command code_typeK "define code syntax for open state monads" K.thy_decl (
    parse_multi_syntax P.xname parse_syntax
    >> (Toplevel.theory oo fold) (fn (target, syns) =>
          fold (fn (raw_tyco, syn) => add_syntax_monad target raw_tyco syn) syns)
  );*)

val code_reservedP =
  OuterSyntax.command code_reservedK "declare words as reserved for target language" K.thy_decl (
    P.name -- Scan.repeat1 P.name
    >> (fn (target, reserveds) => (Toplevel.theory o fold (add_reserved target)) reserveds)
  )

val code_modulenameP =
  OuterSyntax.command code_modulenameK "alias module to other name" K.thy_decl (
    P.name -- Scan.repeat1 (P.name -- P.name)
    >> (fn (target, modlnames) => (Toplevel.theory o fold (add_modl_alias target)) modlnames)
  )

val code_moduleprologP =
  OuterSyntax.command code_moduleprologK "add prolog to module" K.thy_decl (
    P.name -- Scan.repeat1 (P.name -- (P.text >> (fn "-" => NONE | s => SOME s)))
    >> (fn (target, prologs) => (Toplevel.theory o fold (add_modl_prolog target)) prologs)
  )

val _ = OuterSyntax.add_keywords [infixK, infixlK, infixrK];

val _ = OuterSyntax.add_parsers [code_classP, code_instanceP, code_typeP, code_constP,
  code_reservedP, code_modulenameP, code_moduleprologP];

(*including serializer defaults*)
val _ = Context.add_setup (
  gen_add_syntax_tyco (K I) "SML" "fun" (SOME (2, fn fxy => fn pr_typ => fn [ty1, ty2] =>
      (gen_brackify (case fxy of NOBR => false | _ => eval_fxy (INFX (1, R)) fxy) o Pretty.breaks) [
        pr_typ (INFX (1, X)) ty1,
        str "->",
        pr_typ (INFX (1, R)) ty2
      ]))
  #> gen_add_syntax_tyco (K I) "OCaml" "fun" (SOME (2, fn fxy => fn pr_typ => fn [ty1, ty2] =>
      (gen_brackify (case fxy of NOBR => false | _ => eval_fxy (INFX (1, R)) fxy) o Pretty.breaks) [
        pr_typ (INFX (1, X)) ty1,
        str "->",
        pr_typ (INFX (1, R)) ty2
      ]))
  #> gen_add_syntax_tyco (K I) "Haskell" "fun" (SOME (2, fn fxy => fn pr_typ => fn [ty1, ty2] =>
      brackify_infix (1, R) fxy [
        pr_typ (INFX (1, X)) ty1,
        str "->",
        pr_typ (INFX (1, R)) ty2
      ]))
  (*IntInt resp. Big_int are added later when code extraction for numerals is set up*)
  #> add_reserved "SML" "o" (*dictionary projections use it already*)
  #> fold (add_reserved "Haskell") [
      "Prelude", "Main", "Bool", "Maybe", "Either", "Ordering", "Char", "String", "Int",
      "Integer", "Float", "Double", "Rational", "IO", "Eq", "Ord", "Enum", "Bounded",
      "Num", "Real", "Integral", "Fractional", "Floating", "RealFloat", "Monad", "Functor",
      "AlreadyExists", "ArithException", "ArrayException", "AssertionFailed", "AsyncException",
      "BlockedOnDeadMVar", "Deadlock", "Denormal", "DivideByZero", "DotNetException", "DynException",
      "Dynamic", "EOF", "EQ", "EmptyRec", "ErrorCall", "ExitException", "ExitFailure",
      "ExitSuccess", "False", "GT", "HeapOverflow",
      "IO", "IOError", "IOException", "IllegalOperation",
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
    ] (*due to weird handling of ':', we can't do anything else than to import *all* prelude symbols*)

)

end; (*local*)

end; (*struct*)
