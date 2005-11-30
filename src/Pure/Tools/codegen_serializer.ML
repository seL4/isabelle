(*  Title:      Pure/Tools/codegen_serializer.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Serializer from intermediate language ("Thin-gol") to
target languages (like ML or Haskell).
*)

signature CODEGEN_SERIALIZER =
sig
  type primitives;
  val empty_prims: primitives;
  val add_prim: string * (string * string list) -> primitives -> primitives;
  val merge_prims: primitives * primitives -> primitives;
  val has_prim: primitives -> string -> bool;
  val mk_prims: primitives -> string;

  type 'a pretty_syntax = string
    -> (int * (Pretty.T list -> ('a -> Pretty.T) -> Pretty.T)) option;
  type serializer = CodegenThingol.itype pretty_syntax -> CodegenThingol.iexpr pretty_syntax
    -> primitives -> string list option -> CodegenThingol.module -> Pretty.T;

  val ml_from_thingol: string list list -> string -> serializer;
  val haskell_from_thingol: string list list -> string -> serializer;
end;

structure CodegenSerializer: CODEGEN_SERIALIZER =
struct

open CodegenThingol;


(** target language primitives **)

type primitives = string Graph.T;

val empty_prims = Graph.empty;

fun add_prim (f, (def, deps)) prims =
  prims
  |> Graph.new_node (f, def)
  |> fold (fn dep => Graph.add_edge (f, dep)) deps;

val merge_prims = Graph.merge (op =) : primitives * primitives -> primitives;

val has_prim : primitives -> string -> bool = can o Graph.get_node;

fun get_prims prims defs =
  defs
  |> filter (can (Graph.get_node prims))
  |> `I
  ||> Graph.all_succs prims
  ||> (fn gr => Graph.subgraph gr prims)
  ||> Graph.strong_conn
  ||> rev
  ||> Library.flat
  ||> map (Graph.get_node prims)
  ||> separate ""
  ||> cat_lines
  ||> suffix "\n";

fun mk_prims prims = get_prims prims (Graph.keys prims) |> snd;


(** keyword arguments **)

type kw = (string * string option) list;
fun kw_make args =
  let
    val parse_keyval = ();
  in
    Args.!!! (Scan.repeat (
      Args.name
      -- Scan.option (Args.$$$ "=" |-- Args.name)
    ) #> fst) args
  end;
fun kw_get k kw =
  ((the o AList.lookup (op =) kw) k, AList.delete (op =) k kw);
fun kw_has kw k =
  AList.defined (op =) kw k;
fun kw_done x [] = x
  | kw_done x kw =
      error ("uninterpreted keyword arguments: " ^ (commas o map (quote o fst)) kw);



(** generic serialization **)

type 'a pretty_syntax = string
  -> (int * (Pretty.T list -> ('a -> Pretty.T) -> Pretty.T)) option;
type serializer = CodegenThingol.itype pretty_syntax -> CodegenThingol.iexpr pretty_syntax
  -> primitives -> string list option -> CodegenThingol.module -> Pretty.T;

datatype lrx = L | R | X;

datatype brack =
    BR
  | NOBR
  | INFX of (int * lrx);

fun eval_lrx L L = false
  | eval_lrx R R = false
  | eval_lrx _ _ = true;

fun eval_br BR _ = true
  | eval_br NOBR _ = false
  | eval_br (INFX (pr1, lr1)) (INFX (pr2, lr2)) =
      pr1 > pr2
      orelse pr1 = pr2
      andalso eval_lrx lr1 lr2
  | eval_br (INFX _) _ = false;

fun eval_br_postfix BR _ = false
  | eval_br_postfix NOBR _ = false
  | eval_br_postfix (INFX (pr1, lr1)) (INFX (pr2, lr2)) =
      pr1 > pr2
      orelse pr1 = pr2
      andalso eval_lrx lr1 lr2
  | eval_br_postfix (INFX _) _ = false;

fun brackify _ [p] = p
  | brackify true (ps as _::_) = Pretty.enclose "(" ")" (Pretty.breaks ps)
  | brackify false (ps as _::_) = Pretty.block (Pretty.breaks ps);

fun postify [] f = [f]
  | postify [p] f = [p, Pretty.brk 1, f]
  | postify (ps as _::_) f = [Pretty.list "(" ")" ps, Pretty.brk 1, f];

fun upper_first s =
  let val (c :: cs) = String.explode s
  in String.implode (Char.toUpper c :: cs) end;

fun lower_first s =
  let val (c :: cs) = String.explode s
  in String.implode (Char.toLower c :: cs) end;


(** grouping functions **)

fun group_datatypes one_arg defs =
  let
    fun check_typ_dup dtname ts =
      if AList.defined (op =) ts dtname
      then error ("double datatype definition: " ^ quote dtname)
      else ts
    fun check_typ_miss dtname ts =
      if AList.defined (op =) ts dtname
      then ts
      else error ("missing datatype definition: " ^ quote dtname)
    fun group (name, Datatype (vs, _, _)) ts =
          (if one_arg
           then map (fn (_, []) => () | _ => error "can't serialize sort constrained datatype declaration to ML") vs
           else [];
          ts
          |> apsnd (check_typ_dup name)
          |> apsnd (AList.update (op =) (name, (vs, []))))
      | group (name, Datatypecons (dtname, tys as _::_::_)) ts =
          if one_arg
          then error ("datatype constructor containing more than one parameter")
          else
            ts
            |> apfst (AList.default (op =) (NameSpace.base dtname, []))
            |> apfst (AList.map_entry (op =) (NameSpace.base dtname) (cons (name, tys)))
      | group (name, Datatypecons (dtname, tys)) ts =
          ts
          |> apfst (AList.default (op =) (NameSpace.base dtname, []))
          |> apfst (AList.map_entry (op =) (NameSpace.base dtname) (cons (name, tys)))
      | group _ _ =
          error ("Datatype block containing other statements than datatype or constructor definitions")
    fun group_cons (dtname, co) ts =
      ts
      |> check_typ_miss dtname
      |> AList.map_entry (op =) dtname (rpair co o fst)
  in
    ([], [])
    |> fold group defs
    |-> (fn cons => fold group_cons cons)
  end;

fun group_classes defs =
  let
    fun check_class_dup clsname ts =
      if AList.defined (op =) ts clsname
      then error ("double class definition: " ^ quote clsname)
      else ts
    fun check_clsname_miss clsname ts =
      if AList.defined (op =) ts clsname
      then ts
      else error ("missing class definition: " ^ quote clsname)
    fun group (name, Class (supercls, v, _, _)) ts =
          ts
          |> apsnd (check_class_dup name)
          |> apsnd (AList.update (op =) (name, ((supercls, v), [])))
      | group (name, Classmember (clsname, _, ty)) ts =
          ts
          |> apfst (AList.default (op =) (NameSpace.base clsname, []))
          |> apfst (AList.map_entry (op =) (NameSpace.base clsname) (cons (name, ty)))
      | group _ _ =
          error ("Datatype block containing other statements than datatype or constructor definitions")
    fun group_members (clsname, member) ts =
      ts
      |> check_clsname_miss clsname
      |> AList.map_entry (op =) clsname (rpair member o fst)
  in
    ([], [])
    |> fold group defs
    |-> (fn members => fold group_members members)
  end;

(** ML serializer **)

local

fun ml_from_defs tyco_syntax const_syntax resolv ds =
  let
    fun chunk_defs ps =
      let
        val (p_init, p_last) = split_last ps
      in
        Pretty.chunks (p_init @ [Pretty.block ([p_last, Pretty.str ";"])])
    end;
    val ml_label_uniq = translate_string (fn "'" => "''" | "." => "'" | c => c);
    fun ml_from_type br (IType ("Pair", [t1, t2])) =
          brackify (eval_br_postfix br (INFX (2, L))) [
            ml_from_type (INFX (2, X)) t1,
            Pretty.str "*",
            ml_from_type (INFX (2, X)) t2
          ]
      | ml_from_type br (IType ("Bool", [])) =
          Pretty.str "bool"
      | ml_from_type br (IType ("Integer", [])) =
          Pretty.str "IntInf.int"
      | ml_from_type br (IType ("List", [ty])) =
          postify ([ml_from_type BR ty]) (Pretty.str "list")
          |> Pretty.block
      | ml_from_type br (IType (tyco, typs)) =
          let
            val tyargs = (map (ml_from_type BR) typs)
          in
            case tyco_syntax tyco
             of NONE =>
                  postify tyargs ((Pretty.str o resolv) tyco)
                  |> Pretty.block
              | SOME (i, pr) =>
                  if i <> length (typs)
                  then error "can only serialize strictly complete type applications to ML"
                  else pr tyargs (ml_from_type BR)
          end
      | ml_from_type br (IFun (t1, t2)) =
          brackify (eval_br_postfix br (INFX (1, R))) [
            ml_from_type (INFX (1, X)) t1,
            Pretty.str "->",
            ml_from_type (INFX (1, R)) t2
          ]
      | ml_from_type _ (IVarT (v, [])) =
          Pretty.str ("'" ^ v)
      | ml_from_type _ (IVarT (_, sort)) =
          "cannot serialize sort constrained type variable to ML: " ^ commas sort |> error
      | ml_from_type _ (IDictT fs) =
          (Pretty.enclose "{" "}" o Pretty.breaks) (
            map (fn (f, ty) =>
              Pretty.block [Pretty.str (ml_label_uniq f ^ ": "), ml_from_type NOBR ty]) fs
          );
    fun ml_from_pat br (ICons (("True", []), _)) =
          Pretty.str "true"
      | ml_from_pat br (ICons (("False", []), _)) =
          Pretty.str "false"
      | ml_from_pat br (ICons (("Pair", [p1, p2]), _)) =
          Pretty.list "(" ")" [
            ml_from_pat NOBR p1,
            ml_from_pat NOBR p2
          ]
      | ml_from_pat br (ICons (("Nil", []), _)) =
          Pretty.str "[]"
      | ml_from_pat br (p as ICons (("Cons", _), _)) =
          let
            fun dest_cons (ICons (("Cons", [ICons (("Pair", [p1, p2]), _)]), _)) = SOME (p1, p2)
              | dest_cons p = NONE
          in
            case unfoldr dest_cons p
             of (ps, (ICons (("Nil", []), _))) =>
                  ps
                  |> map (ml_from_pat NOBR)
                  |> Pretty.list "[" "]"
              | (ps, p) =>
                  (ps @ [p])
                  |> map (ml_from_pat (INFX (5, X)))
                  |> separate (Pretty.str "::")
                  |> brackify (eval_br br (INFX (5, R)))
          end
      | ml_from_pat br (ICons ((f, ps), ty)) =
          ps
          |> map (ml_from_pat BR)
          |> cons ((Pretty.str o resolv) f)
          |> brackify (eval_br br BR)
      | ml_from_pat br (IVarP (v, IType ("Integer", []))) =
          brackify (eval_br br BR) [
            Pretty.str v,
            Pretty.str ":",
            Pretty.str "IntInf.int"
          ]
      | ml_from_pat br (IVarP (v, _)) =
          Pretty.str v;
    fun ml_from_expr br (e as (IApp (IConst ("Cons", _), _))) =
          let
            fun dest_cons (IApp (IConst ("Cons", _),
                  IApp (IApp (IConst ("Pair", _), e1), e2))) = SOME (e1, e2)
              | dest_cons p = NONE
          in
            case unfoldr dest_cons e
             of (es, (IConst ("Nil", _))) =>
                  es
                  |> map (ml_from_expr NOBR)
                  |> Pretty.list "[" "]"
              | (es, e) =>
                  (es @ [e])
                  |> map (ml_from_expr (INFX (5, X)))
                  |> separate (Pretty.str "::")
                  |> brackify (eval_br br (INFX (5, R)))
          end
      | ml_from_expr br (e as IApp (e1, e2)) =
          (case (unfold_app e)
           of (e as (IConst (f, _)), es) =>
                ml_from_app br (f, es)
            | _ =>
                brackify (eval_br br BR) [
                  ml_from_expr NOBR e1,
                  ml_from_expr BR e2
                ])
      | ml_from_expr br (e as IConst (f, _)) =
          ml_from_app br (f, [])
      | ml_from_expr br (IVarE (v, _)) =
          Pretty.str v
      | ml_from_expr br (IAbs ((v, _), e)) =
          brackify (eval_br br BR) [
            Pretty.str ("fn " ^ v ^ " =>"),
            ml_from_expr NOBR e
          ]
      | ml_from_expr br (e as ICase (_, [_])) =
          let
            val (ps, e) = unfold_let e;
            fun mk_val (p, e) = Pretty.block [
                Pretty.str "val ",
                ml_from_pat BR p,
                Pretty.str " =",
                Pretty.brk 1,
                ml_from_expr NOBR e,
                Pretty.str ";"
              ]
          in Pretty.chunks [
            [Pretty.str ("let"), Pretty.fbrk, map mk_val ps |> Pretty.chunks] |> Pretty.block,
            [Pretty.str ("in"), Pretty.fbrk, ml_from_expr NOBR e] |> Pretty.block,
            Pretty.str ("end")
          ] end
      | ml_from_expr br (ICase (e, c::cs)) =
          let
            fun mk_clause definer (p, e) =
              Pretty.block [
                Pretty.str definer,
                ml_from_pat NOBR p,
                Pretty.str " =>",
                Pretty.brk 1,
                ml_from_expr NOBR e
              ]
          in brackify (eval_br br BR) (
            Pretty.str "case"
            :: ml_from_expr NOBR e
            :: mk_clause "of " c
            :: map (mk_clause "| ") cs
          ) end
      | ml_from_expr br (IInst _) =
          error "cannot serialize poly instant to ML"
      | ml_from_expr br (IDictE fs) =
          (Pretty.enclose "{" "}" o Pretty.breaks) (
            map (fn (f, e) =>
              Pretty.block [Pretty.str (ml_label_uniq f ^ " = "), ml_from_expr NOBR e]) fs
          )
      | ml_from_expr br (ILookup (ls, v)) =
          brackify (eval_br br BR) [
            Pretty.str "(",
            ls |> map ((fn s => "#" ^ s) o ml_label_uniq) |> foldr1 (fn (l, e) => l ^ " o " ^ e) |> Pretty.str,
            Pretty.str ")",
            Pretty.str " ",
            Pretty.str v
          ]
    and mk_app_p br p args =
      brackify (eval_br br BR)
        (p :: map (ml_from_expr BR) args)
    and ml_from_app br ("Nil", []) =
          Pretty.str "[]"
      | ml_from_app br ("True", []) =
          Pretty.str "true"
      | ml_from_app br ("False", []) =
          Pretty.str "false"
      | ml_from_app br ("primeq", [e1, e2]) =
          brackify (eval_br br (INFX (4, L))) [
            ml_from_expr (INFX (4, L)) e1,
            Pretty.str "=",
            ml_from_expr (INFX (4, X)) e2
          ]
      | ml_from_app br ("Pair", [e1, e2]) =
          Pretty.list "(" ")" [
            ml_from_expr NOBR e1,
            ml_from_expr NOBR e2
          ]
      | ml_from_app br ("and", [e1, e2]) =
          brackify (eval_br br (INFX (~1, L))) [
            ml_from_expr (INFX (~1, L)) e1,
            Pretty.str "andalso",
            ml_from_expr (INFX (~1, X)) e2
          ]
      | ml_from_app br ("or", [e1, e2]) =
          brackify (eval_br br (INFX (~2, L))) [
            ml_from_expr (INFX (~2, L)) e1,
            Pretty.str "orelse",
            ml_from_expr (INFX (~2, X)) e2
          ]
      | ml_from_app br ("if", [b, e1, e2]) =
          brackify (eval_br br BR) [
            Pretty.str "if",
            ml_from_expr NOBR b,
            Pretty.str "then",
            ml_from_expr NOBR e1,
            Pretty.str "else",
            ml_from_expr NOBR e2
          ]
      | ml_from_app br ("add", [e1, e2]) =
          brackify (eval_br br (INFX (6, L))) [
            ml_from_expr (INFX (6, L)) e1,
            Pretty.str "+",
            ml_from_expr (INFX (6, X)) e2
          ]
      | ml_from_app br ("mult", [e1, e2]) =
          brackify (eval_br br (INFX (7, L))) [
            ml_from_expr (INFX (7, L)) e1,
            Pretty.str "+",
            ml_from_expr (INFX (7, X)) e2
          ]
      | ml_from_app br ("lt", [e1, e2]) =
          brackify (eval_br br (INFX (4, L))) [
            ml_from_expr (INFX (4, L)) e1,
            Pretty.str "<",
            ml_from_expr (INFX (4, X)) e2
          ]
      | ml_from_app br ("le", [e1, e2]) =
          brackify (eval_br br (INFX (7, L))) [
            ml_from_expr (INFX (4, L)) e1,
            Pretty.str "<=",
            ml_from_expr (INFX (4, X)) e2
          ]
      | ml_from_app br ("minus", es) =
          mk_app_p br (Pretty.str "~") es
      | ml_from_app br ("wfrec", es) =
          mk_app_p br (Pretty.str "wfrec") es
      | ml_from_app br (f, []) =
          Pretty.str (resolv f)
      | ml_from_app br (f, es) =
          case const_syntax f
           of NONE =>
                let
                  val (es', e) = split_last es;
                in mk_app_p br (ml_from_app NOBR (f, es')) [e] end
            | SOME (i, pr) =>
                let
                  val (es1, es2) = splitAt (i, es);
                in mk_app_p br (pr (map (ml_from_expr BR) es1) (ml_from_expr BR)) es2 end;
    fun ml_from_funs (ds as d::ds_tl) =
      let
        fun mk_definer [] = "val"
          | mk_definer _ = "fun"
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
            val lhs = [Pretty.str (definer ^ " " ^ f)]
                       @ (if null pats
                          then [Pretty.str ":", ml_from_type NOBR ty]
                          else map (ml_from_pat BR) pats)
            val rhs = [Pretty.str "=", ml_from_expr NOBR expr]
          in
            Pretty.block (separate (Pretty.brk 1) (lhs @ rhs))
          end
        fun mk_fun definer (f, Fun (eqs as eq::eq_tl, (_, ty))) =
          let
            val (pats_hd::pats_tl) = (fst o split_list) eqs;
            val _ = fold (fn x => fn y => (x ~~ y; y)) pats_tl pats_hd;
              (*check for equal length of argument lists*)
            val shift = if null eq_tl then I else map (Pretty.block o single);
          in (Pretty.block o Pretty.fbreaks o shift) (
               mk_eq definer f ty eq
               :: map (mk_eq "|" f ty) eq_tl
             )
          end
      in
        chunk_defs (
          mk_fun definer d
          :: map (mk_fun "and") ds_tl
        )
      end;
    fun ml_from_datatypes defs =
      let
        fun mk_datatypes (ds as d::ds_tl) =
          let
            fun praetify [] f = [f]
              | praetify [p] f = [f, Pretty.str " of ", p]
            fun mk_cons (co, typs) =
              (Pretty.block oo praetify)
                (map (ml_from_type NOBR) typs)
                (Pretty.str (resolv co))
            fun mk_datatype definer (t, (vs, cs)) =
              Pretty.block (
                [Pretty.str definer]
                @ postify (map (ml_from_type BR o IVarT) vs)
                    (Pretty.str (resolv t))
                @ [Pretty.str " =",
                  Pretty.brk 1]
                @ separate (Pretty.block [Pretty.brk 1, Pretty.str "| "]) (map mk_cons cs)
              )
          in
            chunk_defs (
              mk_datatype "datatype " d
              :: map (mk_datatype "and ") ds_tl
            )
          end;
      in
        (mk_datatypes o group_datatypes true) defs
      end;
    fun ml_from_def (name, Typesyn (vs, ty)) =
        (map (fn (vname, []) => () | _ => error "can't serialize sort constrained type declaration to ML") vs;
         Pretty.block (
          Pretty.str "type "
          :: postify (map (Pretty.str o fst) vs) (Pretty.str name)
          @ [Pretty.str " =",
          Pretty.brk 1,
          ml_from_type NOBR ty,
          Pretty.str ";"
        ]))
      | ml_from_def (name, Nop) =
          if exists (fn query => query name)
            [(fn name => (is_some o tyco_syntax) name),
             (fn name => (is_some o const_syntax) name)]
          then Pretty.str ""
          else error ("empty statement during serialization: " ^ quote name)
      | ml_from_def (name, Class _) =
          error ("can't serialize class declaration " ^ quote name ^ " to ML")
      | ml_from_def (name, Classinst _) =
          error ("can't serialize instance declaration " ^ quote name ^ " to ML")
  in (writeln "******************"; (*map (writeln o Pretty.o)*)
  case (snd o hd) ds
   of Fun _ => ml_from_funs ds
    | Datatypecons _ => ml_from_datatypes ds
    | Datatype _ => ml_from_datatypes ds
    | _ => (case ds of [d] => ml_from_def d))
  end;

in

fun ml_from_thingol nspgrp name_root tyco_syntax const_syntax prims select module =
  let
    fun ml_validator name =
      let
        fun replace_invalid c =
          if (Char.isAlphaNum o the o Char.fromString) c orelse c = "'"
          andalso not (NameSpace.separator = c)
          then c
          else "_"
        fun suffix_it name =
          name
          |> member (op =) ThmDatabase.ml_reserved ? suffix "'"
          |> member (op =) CodegenThingol.prims ? suffix "'"
          |> has_prim prims ? suffix "'"
          |> (fn name' => if name = name' then name else suffix_it name')
      in
        name
        |> translate_string replace_invalid
        |> suffix_it
        |> (fn name' => if name = name' then NONE else SOME name')
    end;
    fun ml_from_module (name, ps) =
      Pretty.chunks ([
        Pretty.str ("structure " ^ name ^ " = "),
        Pretty.str "struct",
        Pretty.str ""
      ] @ separate (Pretty.str "") ps @ [
        Pretty.str "",
        Pretty.str ("end; (* struct " ^ name ^ " *)")
      ]);
    fun eta_expander "Pair" = 2
      | eta_expander "Cons" = 2
      | eta_expander "primeq" = 2
      | eta_expander "and" = 2
      | eta_expander "or" = 2
      | eta_expander "if" = 3
      | eta_expander "add" = 2
      | eta_expander "mult" = 2
      | eta_expander "lt" = 2
      | eta_expander "le" = 2
      | eta_expander s =
          if NameSpace.is_qualified s
          then case get_def module s
            of Datatypecons (_ , tys) =>
                if length tys >= 2 then length tys else 0
             | _ =>
                const_syntax s
                |> Option.map fst
                |> the_default 0
          else 0
  in
    module
    |> debug 12 (Pretty.output o pretty_module)
    |> debug 3 (fn _ => "connecting datatypes and classdecls...")
    |> connect_datatypes_clsdecls
    |> debug 3 (fn _ => "selecting submodule...")
    |> (if is_some select then (partof o the) select else I)
    |> debug 3 (fn _ => "eta-expanding...")
    |> eta_expand eta_expander
    |> debug 3 (fn _ => "eta-expanding polydefs...")
    |> eta_expand_poly
    |> debug 12 (Pretty.output o pretty_module)
    |> debug 3 (fn _ => "tupelizing datatypes...")
    |> tupelize_cons
    |> debug 3 (fn _ => "eliminating classes...")
    |> eliminate_classes
    |> debug 3 (fn _ => "generating...")
    |> serialize (ml_from_defs tyco_syntax const_syntax) ml_from_module ml_validator nspgrp name_root
  end;

fun ml_from_thingol' nspgrp name_root =
  Scan.optional (
    OuterParse.$$$ "(" |-- OuterParse.list1 OuterParse.text --| OuterParse.$$$ ")"
  ) []
    >> (fn _ => ml_from_thingol nspgrp name_root);

(* ML infix precedence
   7 / * div mod
   6 + - ^
   5 :: @
   4 = <> < > <= >=
   3 := o *)

end; (* local *)

local

val bslash = "\\";

fun haskell_from_defs tyco_syntax const_syntax is_cons resolv defs =
  let
    val resolv = fn s =>
      let
        val (prfix, base) = (split_last o NameSpace.unpack o resolv) s
      in
        NameSpace.pack (map upper_first prfix @ [base])
      end;
    fun resolv_const f =
      if is_cons f
      then (upper_first o resolv) f
      else (lower_first o resolv) f
    fun haskell_from_sctxt vs =
      let
        fun from_sctxt [] = Pretty.str ""
          | from_sctxt vs =
              vs
              |> map (fn (v, cls) => Pretty.str ((upper_first o resolv) cls ^ " " ^ lower_first v))
              |> Pretty.gen_list "," "(" ")"
              |> (fn p => Pretty.block [p, Pretty.str " => "])
      in 
        vs
        |> map (fn (v, sort) => map (pair v) sort)
        |> Library.flat
        |> from_sctxt
      end;
    fun haskell_from_type br ty =
      let
        fun from_itype br (IType ("Pair", [t1, t2])) sctxt =
              sctxt
              |> from_itype NOBR t1
              ||>> from_itype NOBR t2
              |-> (fn (p1, p2) => pair (Pretty.gen_list "," "(" ")" [p1, p2]))
          | from_itype br (IType ("List", [ty])) sctxt =
              sctxt
              |> from_itype NOBR ty
              |-> (fn p => pair (Pretty.enclose "[" "]" [p]))
          | from_itype br (IType (tyco, tys)) sctxt =
              let
                fun mk_itype NONE tyargs sctxt =
                      sctxt
                      |> pair (brackify (eval_br br BR) ((Pretty.str o upper_first o resolv) tyco :: tyargs))
                  | mk_itype (SOME (i, pr)) tyargs sctxt =
                      if i <> length (tys)
                      then error "can only serialize strictly complete type applications to haskell"
                      else
                        sctxt
                        |> pair (pr tyargs (haskell_from_type BR))
              in
                sctxt
                |> fold_map (from_itype BR) tys
                |-> mk_itype (tyco_syntax tyco)
              end
          | from_itype br (IFun (t1, t2)) sctxt =
              sctxt
              |> from_itype (INFX (1, X)) t1
              ||>> from_itype (INFX (1, R)) t2
              |-> (fn (p1, p2) => pair (
                    brackify (eval_br br (INFX (1, R))) [
                      p1,
                      Pretty.str "->",
                      p2
                    ]
                  ))
          | from_itype br (IVarT (v, [])) sctxt =
              sctxt
              |> pair ((Pretty.str o lower_first) v)
          | from_itype br (IVarT (v, sort)) sctxt =
              sctxt
              |> AList.default (op =) (v, [])
              |> AList.map_entry (op =) v (fold (insert (op =)) sort)
              |> pair ((Pretty.str o lower_first) v)
          | from_itype br (IDictT _) _ =
              error "cannot serialize dictionary type to haskell"
      in
        []
        |> from_itype br ty
        ||> haskell_from_sctxt
        |> (fn (pty, pctxt) => Pretty.block [pctxt, pty])
      end;
    fun haskell_from_pat br (ICons (("Pair", [p1, p2]), _)) =
          Pretty.list "(" ")" [
            haskell_from_pat NOBR p1,
            haskell_from_pat NOBR p2
          ]
      | haskell_from_pat br (ICons (("Nil", []), _)) =
          Pretty.str "[]"
      | haskell_from_pat br (p as ICons (("Cons", _), _)) =
          let
            fun dest_cons (ICons (("Cons", [p1, p2]), ty)) = SOME (p1, p2)
              | dest_cons p = NONE
          in
            case unfoldr dest_cons p
             of (ps, (ICons (("Nil", []), _))) =>
                  ps
                  |> map (haskell_from_pat NOBR)
                  |> Pretty.list "[" "]"
              | (ps, p) =>
                  (ps @ [p])
                  |> map (haskell_from_pat (INFX (5, X)))
                  |> separate (Pretty.str ":")
                  |> brackify (eval_br br (INFX (5, R)))
          end
      | haskell_from_pat br (ICons ((f, ps), _)) =
          ps
          |> map (haskell_from_pat BR)
          |> cons ((Pretty.str o upper_first o resolv) f)
          |> brackify (eval_br br BR)
      | haskell_from_pat br (IVarP (v, _)) =
          (Pretty.str o lower_first) v;
    fun haskell_from_expr br (e as (IApp (IApp (IConst ("Cons", _), _), _))) =
          let
            fun dest_cons (IApp (IApp (IConst ("Cons", _), e1), e2)) = SOME (e1, e2)
              | dest_cons p = NONE
          in
            case unfoldr dest_cons e
             of (es, (IConst ("Nil", _))) =>
                  es
                  |> map (haskell_from_expr NOBR)
                  |> Pretty.list "[" "]"
              | (es, e) =>
                  (es @ [e])
                  |> map (haskell_from_expr (INFX (5, X)))
                  |> separate (Pretty.str ":")
                  |> brackify (eval_br br (INFX (5, R)))
          end
      | haskell_from_expr br (e as IApp (e1, e2)) =
          (case (unfold_app e)
           of (e as (IConst (f, _)), es) =>
                haskell_from_app br (f, es)
            | _ =>
                brackify (eval_br br BR) [
                  haskell_from_expr NOBR e1,
                  haskell_from_expr BR e2
                ])
      | haskell_from_expr br (e as IConst (f, _)) =
          haskell_from_app br (f, [])
      | haskell_from_expr br (IVarE (v, _)) =
          (Pretty.str o lower_first) v
      | haskell_from_expr br (e as IAbs _) =
          let
            val (vs, body) = unfold_abs e
          in
            brackify (eval_br br BR) (
              Pretty.str bslash
              :: map (Pretty.str o lower_first o fst) vs @ [
              Pretty.str "->",
              haskell_from_expr NOBR body
            ])
          end
      | haskell_from_expr br (e as ICase (_, [_])) =
          let
            val (ps, body) = unfold_let e;
            fun mk_bind (p, e) = Pretty.block [
                haskell_from_pat BR p,
                Pretty.str " =",
                Pretty.brk 1,
                haskell_from_expr NOBR e
              ];
          in Pretty.chunks [
            [Pretty.str ("let"), Pretty.fbrk, map mk_bind ps |> Pretty.chunks] |> Pretty.block,
            [Pretty.str ("in "), haskell_from_expr NOBR body] |> Pretty.block
          ] end
      | haskell_from_expr br (ICase (e, c::cs)) =
          let
            fun mk_clause (p, e) =
              Pretty.block [
                haskell_from_pat NOBR p,
                Pretty.str " ->",
                Pretty.brk 1,
                haskell_from_expr NOBR e
              ]
          in (Pretty.block o Pretty.fbreaks) (
            Pretty.block [Pretty.str "case ", haskell_from_expr NOBR e, Pretty.str " of"]
            :: map (mk_clause) cs
          )end
      | haskell_from_expr br (IInst (e, _)) =
          haskell_from_expr br e
      | haskell_from_expr br (IDictE _) =
          error "cannot serialize dictionary expression to haskell"
      | haskell_from_expr br (ILookup _) =
          error "cannot serialize lookup expression to haskell"
    and mk_app_p br p args =
      brackify (eval_br br BR)
        (p :: map (haskell_from_expr BR) args)
    and haskell_from_app br ("Nil", []) =
          Pretty.str "[]"
      | haskell_from_app br ("Cons", es) =
          mk_app_p br (Pretty.str "(:)") es
      | haskell_from_app br ("primeq", [e1, e2]) =
          brackify (eval_br br (INFX (4, L))) [
            haskell_from_expr (INFX (4, L)) e1,
            Pretty.str "==",
            haskell_from_expr (INFX (4, X)) e2
          ]
      | haskell_from_app br ("Pair", [e1, e2]) =
          Pretty.list "(" ")" [
            haskell_from_expr NOBR e1,
            haskell_from_expr NOBR e2
          ]
      | haskell_from_app br ("and", [e1, e2]) =
          brackify (eval_br br (INFX (3, R))) [
            haskell_from_expr (INFX (3, X)) e1,
            Pretty.str "&&",
            haskell_from_expr (INFX (3, R)) e2
          ]
      | haskell_from_app br ("or", [e1, e2]) =
          brackify (eval_br br (INFX (2, L))) [
            haskell_from_expr (INFX (2, L)) e1,
            Pretty.str "||",
            haskell_from_expr (INFX (2, X)) e2
          ]
      | haskell_from_app br ("if", [b, e1, e2]) =
          brackify (eval_br br BR) [
            Pretty.str "if",
            haskell_from_expr NOBR b,
            Pretty.str "then",
            haskell_from_expr NOBR e1,
            Pretty.str "else",
            haskell_from_expr NOBR e2
          ]
      | haskell_from_app br ("add", [e1, e2]) =
          brackify (eval_br br (INFX (6, L))) [
            haskell_from_expr (INFX (6, L)) e1,
            Pretty.str "+",
            haskell_from_expr (INFX (6, X)) e2
          ]
      | haskell_from_app br ("mult", [e1, e2]) =
          brackify (eval_br br (INFX (7, L))) [
            haskell_from_expr (INFX (7, L)) e1,
            Pretty.str "*",
            haskell_from_expr (INFX (7, X)) e2
          ]
      | haskell_from_app br ("lt", [e1, e2]) =
          brackify (eval_br br (INFX (4, L))) [
            haskell_from_expr (INFX (4, L)) e1,
            Pretty.str "<",
            haskell_from_expr (INFX (4, X)) e2
          ]
      | haskell_from_app br ("le", [e1, e2]) =
          brackify (eval_br br (INFX (7, L))) [
            haskell_from_expr (INFX (4, L)) e1,
            Pretty.str "<=",
            haskell_from_expr (INFX (4, X)) e2
          ]
      | haskell_from_app br ("minus", es) =
          mk_app_p br (Pretty.str "negate") es
      | haskell_from_app br ("wfrec", es) =
          mk_app_p br (Pretty.str "wfrec") es
      | haskell_from_app br (f, []) =
          Pretty.str (resolv_const f)
      | haskell_from_app br (f, es) =
          case const_syntax f
           of NONE =>
                let
                  val (es', e) = split_last es;
                in mk_app_p br (haskell_from_app NOBR (f, es')) [e] end
            | SOME (i, pr) =>
                let
                  val (es1, es2) = splitAt (i, es);
                in mk_app_p br (pr (map (haskell_from_expr BR) es1) (haskell_from_expr BR)) es2 end;
    fun haskell_from_datatypes defs =
      let
        fun mk_cons (co, typs) =
            (Pretty.block o Pretty.breaks) (
              Pretty.str ((upper_first o resolv) co)
              :: map (haskell_from_type NOBR) typs
            )
        fun mk_datatype (t, (vs, cs)) =
          Pretty.block (
            Pretty.str "data "
            :: haskell_from_sctxt vs
            :: Pretty.str (upper_first t)
            :: Pretty.block (map (fn (v, _) => Pretty.str (" " ^ (lower_first) v)) vs)
            :: Pretty.str " ="
            :: Pretty.brk 1
            :: separate (Pretty.block [Pretty.brk 1, Pretty.str "| "]) (map mk_cons cs)
          )
      in
        Pretty.chunks ((separate (Pretty.str "") o map mk_datatype o group_datatypes false) defs)
      end;
    fun haskell_from_classes defs =
      let
        fun mk_member (f, ty) =
          Pretty.block [
            Pretty.str (f ^ " ::"),
            Pretty.brk 1,
            haskell_from_type NOBR ty
          ];
        fun mk_class (clsname, ((supclsnames, v), members)) =
          Pretty.block [
            Pretty.str "class ",
            haskell_from_sctxt (map (fn class => (v, [class])) supclsnames),
            Pretty.str ((upper_first clsname) ^ " " ^ v),
            Pretty.str " where",
            Pretty.fbrk,
            Pretty.chunks (map mk_member members)
          ];
      in
        Pretty.chunks ((separate (Pretty.str "") o map mk_class o group_classes) defs)
      end;
    fun haskell_from_def (name, Nop) =
          if exists (fn query => query name)
            [(fn name => (is_some o tyco_syntax) name),
             (fn name => (is_some o const_syntax) name)]
          then Pretty.str ""
          else error ("empty statement during serialization: " ^ quote name)
      | haskell_from_def (name, Fun (eqs, (_, ty))) =
          let
            fun from_eq name (args, rhs) =
              Pretty.block [
                Pretty.str (lower_first name),
                Pretty.block (map (fn p => Pretty.block [Pretty.brk 1, haskell_from_pat BR p]) args),
                Pretty.brk 1,
                Pretty.str ("="),
                Pretty.brk 1,
                haskell_from_expr NOBR rhs
              ]
          in
            Pretty.chunks [
              Pretty.block [
                Pretty.str (name ^ " ::"),
                Pretty.brk 1,
                haskell_from_type NOBR ty
              ],
              Pretty.chunks (map (from_eq name) eqs)
            ]
          end
      | haskell_from_def (name, Typesyn (vs, ty)) =
          Pretty.block [
            Pretty.str "type ",
            haskell_from_sctxt vs,
            Pretty.str (upper_first name),
            Pretty.block (map (fn (v, _) => Pretty.str (" " ^ (lower_first) v)) vs),
            Pretty.str " =",
            Pretty.brk 1,
            haskell_from_type NOBR ty
          ]
      | haskell_from_def (_, Classinst (clsname, (tyco, arity), instmems)) = 
          Pretty.block [
            Pretty.str "instance ",
            haskell_from_sctxt arity,
            Pretty.str ((upper_first o resolv) clsname),
            Pretty.str " ",
            Pretty.str ((upper_first o resolv) tyco),
            Pretty.str " where",
            Pretty.fbrk,
            Pretty.chunks (map (fn (member, const) =>
              Pretty.str ((lower_first o resolv) member ^ " = " ^ (lower_first o resolv) const)
            ) instmems)
          ];
  in case (snd o hd) defs
   of Datatypecons _ => haskell_from_datatypes defs
    | Datatype _ => haskell_from_datatypes defs
    | Class _ => haskell_from_classes defs
    | Classmember _ => haskell_from_classes defs
    | _ => Pretty.block (map haskell_from_def defs |> separate (Pretty.str ""))
  end;

in

fun haskell_from_thingol nspgrp name_root tyco_syntax const_syntax prims select module =
  let
    fun haskell_from_module (name, ps) =
      Pretty.block [
          Pretty.str ("module " ^ (upper_first name) ^ " where"),
          Pretty.fbrk,
          Pretty.fbrk,
          Pretty.chunks (separate (Pretty.str "") ps)
        ];
    fun haskell_validator s = NONE;
    fun eta_expander "Pair" = 2
      | eta_expander "if" = 3
      | eta_expander s =
          if NameSpace.is_qualified s
          then case get_def module s
            of Datatypecons (_ , tys) =>
                if length tys >= 2 then length tys else 0
             | _ =>
                const_syntax s
                |> Option.map fst
                |> the_default 0
          else 0;
    fun is_cons f =
      NameSpace.is_qualified f
      andalso case get_def module f
       of Datatypecons _ => true
        | _ => false;
  in
    module
    |> debug 12 (Pretty.output o pretty_module)
    |> debug 3 (fn _ => "connecting datatypes and classdecls...")
    |> connect_datatypes_clsdecls
    |> debug 3 (fn _ => "selecting submodule...")
    |> (if is_some select then (partof o the) select else I)
    |> debug 3 (fn _ => "eta-expanding...")
    |> eta_expand eta_expander
    |> debug 3 (fn _ => "generating...")
    |> serialize (haskell_from_defs tyco_syntax const_syntax is_cons) haskell_from_module haskell_validator nspgrp name_root
  end;

end; (* local *)

end; (* struct *)

