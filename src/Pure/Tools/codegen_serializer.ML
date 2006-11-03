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
  val get_serializer: theory -> string -> Args.T list
    -> string list option -> CodegenThingol.code -> unit;
  val assert_serializer: theory -> string -> string;

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

datatype 'a mixfix =
    Arg of fixity
  | Pretty of Pretty.T;

fun mk_mixfix (fixity_this, mfx) =
  let
    fun is_arg (Arg _) = true
      | is_arg _ = false;
    val i = (length o List.filter is_arg) mfx;
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
  case f args
   of (x, []) => x
    | (_, _) => error "bad serializer arguments";


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


(* misc *)

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

fun dest_name name =
  let
    val (names, name_base) = (split_last o NameSpace.unpack) name;
    val (names_mod, name_shallow) = split_last names;
  in (names_mod, (name_shallow, name_base)) end;



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
                    ((Pretty.block o Pretty.breaks) [str "fn", str (CodegenThingol.lookup_var vars' v), str "=>"], vars')
                  end
              | pr ((v, SOME p), _) vars =
                  let
                    val vars' = CodegenThingol.intro_vars [v] vars;
                    val vs = CodegenThingol.fold_varnames (insert (op =)) p [];
                    val vars'' = CodegenThingol.intro_vars vs vars';
                  in
                    ((Pretty.block o Pretty.breaks) [str "fn", str (CodegenThingol.lookup_var vars' v), str "as",
                      pr_term vars'' NOBR p, str "=>"], vars'')
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
                val vars' = CodegenThingol.intro_vars vs vars;
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
                val vars' = CodegenThingol.intro_vars vs vars;
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
                      |> CodegenThingol.intro_vars consts
                      |> CodegenThingol.intro_vars ((fold o CodegenThingol.fold_unbound_varnames) (insert (op =)) (t :: ts) []);
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
                  |> CodegenThingol.intro_vars consts;
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

val sml_code_width = ref 80;

fun seri_sml output reserved_user module_alias module_prolog
  (_ : string -> (string * (string -> string option)) option) tyco_syntax const_syntax code =
  let
    datatype node =
        Def of string * ml_def option
      | Module of string * ((Name.context * Name.context) * node Graph.T);
    val empty_names = Name.make_context ("nil" :: ThmDatabase.ml_reserved @ reserved_user);
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
    val init_vars = CodegenThingol.make_vars (ThmDatabase.ml_reserved @ reserved_user);
    fun name_modl modl =
      let
        val modlname = NameSpace.pack modl
      in case module_alias modlname
       of SOME modlname' => NameSpace.unpack modlname'
        | NONE => map (fn name => (the_single o fst)
            (Name.variants [name] empty_names)) modl
      end;
    fun name_def upper base nsp =
      let
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
              map_nsp_fun (name_def false (NameSpace.base name)) >> (fn base => (base, (name, info)))
          | (name, def) => error ("Function block containing illegal def: " ^ quote name)
        ) defs
      >> (split_list #> apsnd MLFuns);
    fun mk_datatype defs =
      fold_map
        (fn (name, CodegenThingol.Datatype info) =>
              map_nsp_typ (name_def false (NameSpace.base name)) >> (fn base => (base, SOME (name, info)))
          | (name, CodegenThingol.Datatypecons _) =>
              map_nsp_fun (name_def true (NameSpace.base name)) >> (fn base => (base, NONE))
          | (name, def) => error ("Datatype block containing illegal def: " ^ quote name)
        ) defs
      >> (split_list #> apsnd (map_filter I
        #> (fn [] => error ("Datatype block without data: " ^ (commas o map (quote o fst)) defs)
             | infos => MLDatas infos)));
    fun mk_class defs =
      fold_map
        (fn (name, CodegenThingol.Class info) =>
              map_nsp_typ (name_def false (NameSpace.base name)) >> (fn base => (base, SOME (name, info)))
          | (name, CodegenThingol.Classop _) =>
              map_nsp_fun (name_def true (NameSpace.base name)) >> (fn base => (base, NONE))
          | (name, def) => error ("Class block containing illegal def: " ^ quote name)
        ) defs
      >> (split_list #> apsnd (map_filter I
        #> (fn [] => error ("Class block without class: " ^ (commas o map (quote o fst)) defs)
             | [info] => MLClass info)));
    fun mk_inst [(name, CodegenThingol.Classinst info)] =
      map_nsp_fun (name_def false (NameSpace.base name))
      >> (fn base => ([base], MLClassinst (name, info)));
    fun add_group mk defs nsp_nodes =
      let
        val names as (name :: names') = map fst defs;
(*         val _ = writeln ("adding " ^ commas names);  *)
        val deps =
          []
          |> fold (fold (insert (op =)) o Graph.imm_succs code) names
          |> subtract (op =) names;
        val (modls, defnames) = (split_list o map dest_name) names;
        val modl = (the_single o distinct (op =)) modls
          handle Empty =>
            error ("Illegal mutual dependencies: " ^ (commas o map fst) defs);
        val modl' = name_modl modl;
        fun add_dep defname name'' =
          let
            val (modl'', defname'') = (apfst name_modl o dest_name) name'';
(*             val _ = writeln (uncurry NameSpace.append defname ^ " -> " ^ name'');  *)
(*             val _ = (writeln o NameSpace.pack) modl';  *)
(*             val _ = (writeln o NameSpace.pack) modl'';  *)
          in if modl' = modl'' then
            map_node modl'
              (Graph.add_edge (NameSpace.pack (modl @ [fst defname, snd defname]), name''))
          else let
            val (common, (diff1::_, diff2::_)) = chop_prefix (op =) (modl', modl'');
          in
            map_node common
              (fn gr => Graph.add_edge_acyclic (diff1, diff2) gr
                handle Graph.CYCLES _ => error ("Dependency "
                  ^ quote (NameSpace.pack (modl' @ [fst defname, snd defname]))
                  ^ " -> " ^ quote name'' ^ " would result in module dependency cycle"))
          end end;
      in
        nsp_nodes
        |> map_nsp_yield modl' (mk defs)
        |-> (fn (base' :: bases', def') =>
           apsnd (map_node modl' (Graph.new_node (name, (Def (base', SOME def')))
              #> fold2 (fn name' => fn base' => Graph.new_node (name', (Def (base', NONE)))) names' bases')))
        |> apsnd (fold (fn defname => fold (add_dep defname) deps) defnames)
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
(*         val _ = writeln ("resolving " ^ name)  *)
        val (modl, _) = apsnd (uncurry NameSpace.append) (dest_name name);
        val modl' = name_modl modl;
        val (_, (_, remainder)) = chop_prefix (op =) (prefix, modl');
        val defname' =
          nodes
          |> fold (fn m => fn g => case Graph.get_node g m
              of Module (_, (_, g)) => g) modl'
          |> (fn g => case Graph.get_node g name of Def (defname, _) => defname);
      in NameSpace.pack (remainder @ [defname']) end;
    fun the_prolog modlname = case module_prolog modlname
     of NONE => []
      | SOME p => [p, str ""];
    fun pr_node prefix (Def (_, NONE)) =
          NONE
      | pr_node prefix (Def (_, SOME def)) =
          SOME (pr_sml_def tyco_syntax const_syntax init_vars (deresolver prefix) def)
      | pr_node prefix (Module (dmodlname, (_, nodes))) =
          (SOME o Pretty.chunks) ([
            str ("structure " ^ dmodlname ^ " = "),
            str "struct",
            str ""
          ] @ the_prolog (NameSpace.pack (prefix @ [dmodlname]))
            @ separate (str "") ((map_filter (pr_node (prefix @ [dmodlname]) o Graph.get_node nodes)
                o rev o flat o Graph.strong_conn) nodes) @ [
            str "",
            str ("end; (*struct " ^ dmodlname ^ "*)")
          ]);
    val p = Pretty.chunks ([
        str ("structure ROOT = "),
        str "struct",
        str ""
      ] @ the_prolog ""
        @ separate (str "") ((map_filter (pr_node [] o Graph.get_node nodes)
            o rev o flat o Graph.strong_conn) nodes) @ [
        str "",
        str ("end; (*struct ROOT*)")
      ]);
  in output p end;

val isar_seri_sml =
  let
    fun output_file file p = File.write (Path.unpack file) (Pretty.output p ^ "\n");
    fun output_diag p = Pretty.writeln p;
    fun output_internal p = use_text Output.ml_output false (Pretty.output p);
  in
    parse_args ((Args.$$$ "-" >> K output_diag
      || Args.$$$ "*" >> K output_internal
      || Args.name >> output_file)
    >> (fn output => seri_sml output))
  end;



(** Haskell serializer **)

fun pr_haskell class_syntax tyco_syntax const_syntax keyword_vars deresolv_here deresolv deriving_show def =
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
                    ((Pretty.block o Pretty.breaks) [str (CodegenThingol.lookup_var vars' v),
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
                val vars' = CodegenThingol.intro_vars vs vars;
              in
                ((Pretty.block o Pretty.breaks) [
                  pr_term vars' BR p,
                  str "=",
                  pr_term vars NOBR t
                ], vars')
              end;
            val (binds, vars') = fold_map pr ts vars;
          in Pretty.chunks [
            [str "(let", Pretty.fbrk, binds |> Pretty.chunks] |> Pretty.block,
            [str "in ", pr_term vars' NOBR t, str ")"] |> Pretty.block
          ] end
      | pr_term vars fxy (ICase ((td, _), bs)) =
          let
            fun pr (p, t) =
              let
                val vs = CodegenThingol.fold_varnames (insert (op =)) p [];
                val vars' = CodegenThingol.intro_vars vs vars;
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
            val tyvars = CodegenThingol.intro_vars (map fst vs) keyword_vars;
            fun pr_eq (ts, t) =
              let
                val consts = map_filter
                  (fn c => if (is_some o const_syntax) c
                    then NONE else (SOME o NameSpace.base o deresolv) c)
                    ((fold o CodegenThingol.fold_constnames) (insert (op =)) (t :: ts) []);
                val vars = keyword_vars
                  |> CodegenThingol.intro_vars consts
                  |> CodegenThingol.intro_vars ((fold o CodegenThingol.fold_unbound_varnames) (insert (op =)) (t :: ts) []);
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
          end
      | pr_def (name, CodegenThingol.Datatype (vs, [(co, [ty])])) =
          let
            val tyvars = CodegenThingol.intro_vars (map fst vs) keyword_vars;
          in
            (Pretty.block o Pretty.breaks) ([
              str "newtype",
              pr_typscheme_expr tyvars (vs, (deresolv_here name, map (ITyVar o fst) vs)),
              str "=",
              (str o deresolv_here) co,
              pr_typ tyvars BR ty
            ] @ (if deriving_show name then [str "deriving (Read, Show)"] else []))
          end
      | pr_def (name, CodegenThingol.Datatype (vs, co :: cos)) =
          let
            val tyvars = CodegenThingol.intro_vars (map fst vs) keyword_vars;
            fun pr_co (co, tys) =
              (Pretty.block o Pretty.breaks) (
                (str o deresolv_here) co
                :: map (pr_typ tyvars BR) tys
              )
          in
            (Pretty.block o Pretty.breaks) ((
              str "data"
              :: pr_typscheme_expr tyvars (vs, (deresolv_here name, map (ITyVar o fst) vs))
              :: str "="
              :: pr_co co
              :: map ((fn p => Pretty.block [str "| ", p]) o pr_co) cos
            ) @ (if deriving_show name then [str "deriving (Read, Show)"] else []))
          end
      | pr_def (name, CodegenThingol.Class (superclasss, (v, classops))) =
          let
            val tyvars = CodegenThingol.intro_vars [v] keyword_vars;
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
              str (deresolv_here name ^ " " ^ CodegenThingol.lookup_var tyvars v),
              str " where",
              Pretty.fbrk,
              Pretty.chunks (map pr_classop classops)
            ]
          end
      | pr_def (_, CodegenThingol.Classinst ((class, (tyco, vs)), (_, classop_defs))) =
          let
            val tyvars = CodegenThingol.intro_vars (map fst vs) keyword_vars;
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
                    |> CodegenThingol.intro_vars consts;
                in
                  (Pretty.block o Pretty.breaks) [
                    (str o classop_name class) classop,
                    str "=",
                    pr_term vars NOBR t
                  ]
                end
              ) classop_defs)
            ]
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
    val _ = Option.map File.assert destination;
    val empty_names = Name.make_context (reserved_haskell @ reserved_user);
    fun name_modl modl =
      let
        val modlname = NameSpace.pack modl
      in (modlname, case module_alias modlname
       of SOME modlname' => (case module_prefix
            of NONE => modlname'
             | SOME module_prefix => NameSpace.append module_prefix modlname')
        | NONE => NameSpace.pack (map_filter I (module_prefix :: map (fn name => (SOME o the_single o fst)
            (Name.variants [name] empty_names)) modl)))
      end;
    fun add_def (name, (def, deps)) =
      let
        fun name_def base nsp = nsp |>  Name.variants [base] |>> the_single;
        val (modl, (shallow, base)) = dest_name name;
        fun add_name (nsp as (nsp_fun, nsp_typ)) =
          let
            val base' = if member (op =)
              [CodegenNames.nsp_class, CodegenNames.nsp_tyco, CodegenNames.nsp_dtco] shallow
              then first_upper base else base;
          in case def
           of CodegenThingol.Bot => (base', nsp)
            | CodegenThingol.Fun _ => let val (base'', nsp_fun') = name_def base' nsp_fun in (base'', (nsp_fun', nsp_typ)) end
            | CodegenThingol.Datatype _ => let val (base'', nsp_typ') = name_def base' nsp_typ in (base'', (nsp_fun, nsp_typ')) end
            | CodegenThingol.Datatypecons _ => let val (base'', nsp_fun') = name_def base' nsp_fun in (base'', (nsp_fun', nsp_typ)) end
            | CodegenThingol.Class _ => let val (base'', nsp_typ') = name_def base' nsp_typ in (base'', (nsp_fun, nsp_typ')) end
            | CodegenThingol.Classop _ => let val (base'', nsp_fun') = name_def base' nsp_fun in (base'', (nsp_fun', nsp_typ)) end
            | CodegenThingol.Classinst _ => (base', nsp)
          end;
        val (modlname, modlname') = name_modl modl;
        val deps' = remove (op =) modlname (map (NameSpace.qualifier o NameSpace.qualifier) deps);
        fun add_def base' =
          case def
           of CodegenThingol.Bot => I
            | CodegenThingol.Datatypecons _ => I
                cons (name, ((NameSpace.append modlname' base', base'), NONE))
            | CodegenThingol.Classop _ =>
                cons (name, ((NameSpace.append modlname' base', base'), NONE))
            | _ => cons (name, ((NameSpace.append modlname' base', base'), SOME def));
      in
        Symtab.map_default (modlname, (modlname', ([], ([], (empty_names, empty_names)))))
            ((apsnd o apfst) (fold (insert (op =)) deps'))
        #> `(fn code => add_name ((snd o snd o snd o the o Symtab.lookup code) modlname))
        #-> (fn (base', names) =>
              Symtab.map_entry modlname ((apsnd o apsnd) (fn (defs, _) =>
              (add_def base' defs, names))))
      end;
    val code' =
      fold add_def (AList.make (fn name => (Graph.get_node code name, Graph.imm_succs code name))
        (Graph.strong_conn code |> flat)) Symtab.empty;
    val init_vars = CodegenThingol.make_vars (reserved_haskell @ reserved_user);
    fun deresolv name =
      (fst o fst o the o AList.lookup (op =) ((fst o snd o snd o the
        o Symtab.lookup code') ((NameSpace.qualifier o NameSpace.qualifier) name))) name;
    fun deresolv_here name =
      (snd o fst o the o AList.lookup (op =) ((fst o snd o snd o the
        o Symtab.lookup code') ((NameSpace.qualifier o NameSpace.qualifier) name))) name;
    val deresolv_module = fst o the o Symtab.lookup code';
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
    val seri_def = pr_haskell class_syntax tyco_syntax const_syntax init_vars
      deresolv_here deresolv (if string_classes then deriving_show else K false);
    fun write_module (SOME destination) modlname p =
          let
            val filename = case modlname
             of "" => Path.unpack "Main.hs"
              | _ => (Path.ext "hs" o Path.unpack o implode o separate "/" o NameSpace.unpack) modlname;
            val pathname = Path.append destination filename;
            val _ = File.mkdir (Path.dir pathname);
          in File.write pathname (Pretty.setmp_margin 999999 Pretty.output p ^ "\n") end
      | write_module NONE _ p =
          writeln (Pretty.setmp_margin 999999 Pretty.output p ^ "\n");
    fun seri_module (modlname, (modlname', (imports, (defs, _)))) =
      Pretty.chunks (
        str ("module " ^ modlname' ^ " where")
        :: map str (distinct (op =) (map (prefix "import qualified " o deresolv_module) imports)) @ (
        (case module_prolog modlname
         of SOME prolog => [str "", prolog, str ""]
          | NONE => [str ""])
        @ separate (str "") (map_filter
          (fn (name, (_, SOME def)) => SOME (seri_def (name, def))
            | (_, (_, NONE)) => NONE) defs))
      ) |> write_module destination modlname';
  in Symtab.fold (fn modl => fn () => seri_module modl) code' () end;

val isar_seri_haskell =
  parse_args (Scan.option (Args.$$$ "root" -- Args.colon |-- Args.name)
    -- Scan.optional (Args.$$$ "string_classes" >> K true) false
    -- (Args.$$$ "-" >> K NONE || Args.name >> SOME)
    >> (fn ((module_prefix, string_classes), destination) =>
      seri_haskell module_prefix (Option.map Path.unpack destination) string_classes));


(** diagnosis serializer **)

fun seri_diagnosis _ _ _ _ _ code =
  let
    val init_vars = CodegenThingol.make_vars reserved_haskell;
    val pr = pr_haskell (K NONE) (K NONE) (K NONE) init_vars I I (K false);
  in
    []
    |> Graph.fold (fn (name, (def, _)) => case try pr (name, def) of SOME p => cons p | NONE => I) code
    |> separate (Pretty.str "")
    |> Pretty.chunks
    |> Pretty.writeln
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
  #> add_serializer ("Haskell", isar_seri_haskell)
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

val eval_verbose = ref false;

fun eval_term thy ((ref_name, reff), t) code =
  let
    val val_name = "eval.VALUE.EVAL";
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
    |> seri_sml I reserved (Symtab.lookup alias) (Symtab.lookup prolog)
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
      o (Symtab.lookup ((CodegenSerializerData.get) thy))
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
    |> gen_add_syntax_const (K I) target cons' (SOME pr)
  end;

fun add_pretty_ml_string target nill cons str mk_char mk_string target_implode thy =
  let
    val [(_, nil''), (_, cons''), (str', _)] = idfs_of_const_names thy [nill, cons, str];
    val pr = pretty_ml_string nil'' cons'' mk_char mk_string target_implode;
  in
    thy
    |> gen_add_syntax_const (K I) target str' (SOME pr)
  end;

fun add_undefined target undef target_undefined thy =
  let
    val [(undef', _)] = idfs_of_const_names thy [undef];
    fun pretty _ _ _ = str target_undefined;
  in
    thy
    |> gen_add_syntax_const (K I) target undef' (SOME (~1, pretty))
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

val _ = Context.add_setup (
  gen_add_syntax_tyco (K I) "SML" "fun" (SOME (2, fn fxy => fn pr_typ => fn [ty1, ty2] =>
      (gen_brackify (case fxy of BR => false | _ => eval_fxy (INFX (1, R)) fxy) o Pretty.breaks) [
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
  #> add_reserved "Haskell" "Show"
  #> add_reserved "Haskell" "Read"
)

end; (*local*)

end; (*struct*)
