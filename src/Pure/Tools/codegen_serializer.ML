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

  type 'a pretty_syntax = string -> Pretty.T list -> ('a -> Pretty.T)
    -> (string list * Pretty.T) option;
  type serializer = CodegenThingol.itype pretty_syntax -> CodegenThingol.iexpr pretty_syntax
    -> primitives -> string list option -> CodegenThingol.module -> Pretty.T;

  val ml_from_thingol: string list list -> string -> serializer;
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


(** generic serialization **)

type 'a pretty_syntax = string -> Pretty.T list -> ('a -> Pretty.T)
  -> (string list * Pretty.T) option;
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

fun praetify [] f = [f]
  | praetify [p] f = [f, Pretty.str " of ", p]


(** ML serializer **)

local

fun ml_validator prims name =
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

val ml_label_uniq = translate_string (fn "'" => "''" | "." => "'" | c => c);

fun ml_from_defs styco sconst resolv ds =
  let
    fun chunk_defs ps = 
      let
        val (p_init, p_last) = split_last ps
      in
        Pretty.chunks (p_init @ [Pretty.block ([p_last, Pretty.str ";"])])
    end;
    fun ml_from_typ br (IType ("Pair", [t1, t2])) =
          brackify (eval_br_postfix br (INFX (2, L))) [
            ml_from_typ (INFX (2, X)) t1,
            Pretty.str "*",
            ml_from_typ (INFX (2, X)) t2
          ]
      | ml_from_typ br (IType ("Bool", [])) =
          Pretty.str "bool"
      | ml_from_typ br (IType ("Integer", [])) =
          Pretty.str "IntInf.int"
      | ml_from_typ br (IType ("List", [ty])) =
          postify ([ml_from_typ BR ty]) (Pretty.str "list")
          |> Pretty.block
      | ml_from_typ br (IType (tyco, typs)) =
          let
            val tyargs = (map (ml_from_typ BR) typs)
          in
            case styco tyco tyargs (ml_from_typ BR)
             of NONE =>
                  postify tyargs ((Pretty.str o resolv) tyco)
                  |> Pretty.block
              | SOME ([], p) =>
                  p
              | SOME (_, p) =>
                  error ("cannot serialize partial type application to ML, while serializing "
                    ^ quote (tyco ^ " " ^ Pretty.output (Pretty.list "(" ")" tyargs)))
          end
      | ml_from_typ br (IFun (t1, t2)) =
          brackify (eval_br_postfix br (INFX (1, R))) [
            ml_from_typ (INFX (1, X)) t1,
            Pretty.str "->",
            ml_from_typ (INFX (1, R)) t2
          ]
      | ml_from_typ _ (IVarT (v, [])) =
          Pretty.str ("'" ^ v)
      | ml_from_typ _ (IVarT (_, sort)) =
          "cannot serialize sort constrained type variable to ML: " ^ commas sort |> error
      | ml_from_typ _ (IDictT fs) =
          (Pretty.enclose "{" "}" o Pretty.breaks) (
            map (fn (f, ty) =>
              Pretty.block [Pretty.str (ml_label_uniq f ^ ": "), ml_from_typ NOBR ty]) fs
          );
    fun ml_from_pat br (ICons (("True", []), _)) =
          Pretty.str "true"
      | ml_from_pat br (ICons (("False", []), _)) =
          Pretty.str "false"
      | ml_from_pat br (ICons (("Pair", ps), _)) =
          ps
          |> map (ml_from_pat NOBR)
          |> Pretty.list "(" ")"
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
          Pretty.str ("(" ^ v ^ ":IntInf.int)")
      | ml_from_pat br (IVarP (v, _)) =
          Pretty.str v;
    fun ml_from_iexpr br (e as (IApp (IConst ("Cons", _), _))) =
          let
            fun dest_cons (IApp (IConst ("Cons", _),
                  IApp (IApp (IConst ("Pair", _), e1), e2))) = SOME (e1, e2)
              | dest_cons p = NONE
          in
            case unfoldr dest_cons e
             of (es, (IConst ("Nil", _))) =>
                  es
                  |> map (ml_from_iexpr NOBR) 
                  |> Pretty.list "[" "]"
              | (es, e) =>
                  (es @ [e])
                  |> map (ml_from_iexpr (INFX (5, X)))
                  |> separate (Pretty.str "::")
                  |> brackify (eval_br br (INFX (5, R)))
          end
      | ml_from_iexpr br (e as IApp (e1, e2)) =
          (case (unfold_app e)
           of (e as (IConst (f, _)), es) =>
                ml_from_app br (f, es)
            | _ => 
                brackify (eval_br br BR) [
                  ml_from_iexpr NOBR e1,
                  ml_from_iexpr BR e2
                ])
      | ml_from_iexpr br (e as IConst (f, _)) =
          ml_from_app br (f, [])
      | ml_from_iexpr br (IVarE (v, _)) =
          Pretty.str v
      | ml_from_iexpr br (IAbs ((v, _), e)) =
          brackify (eval_br br BR) [
            Pretty.str ("fn " ^ v ^ " =>"),
            ml_from_iexpr BR e
          ]
      | ml_from_iexpr br (e as ICase (_, [_])) =
          let
            val (ps, e) = unfold_let e;
            fun mk_val (p, e) = Pretty.block [
                Pretty.str "val ",
                ml_from_pat BR p,
                Pretty.str " =",
                Pretty.brk 1,
                ml_from_iexpr NOBR e,
                Pretty.str ";"
              ]
          in Pretty.chunks [
            [Pretty.str ("let"), Pretty.fbrk, map mk_val ps |> Pretty.chunks] |> Pretty.block,
            [Pretty.str ("in"), Pretty.fbrk, ml_from_iexpr NOBR e] |> Pretty.block,
            Pretty.str ("end")
          ] end
      | ml_from_iexpr br (ICase (e, c::cs)) =
          let
            fun mk_clause definer (p, e) =
              Pretty.block [
                Pretty.str definer,
                ml_from_pat NOBR p,
                Pretty.str " =>",
                Pretty.brk 1,
                ml_from_iexpr NOBR e
              ]
          in brackify (eval_br br BR) (
            Pretty.str "case "
            :: ml_from_iexpr NOBR e
            :: mk_clause "of " c
            :: map (mk_clause "|") cs
          ) end
      | ml_from_iexpr br (IInst _) =
          error "cannot serialize poly instant to ML"
      | ml_from_iexpr br (IDictE fs) =
          (Pretty.enclose "{" "}" o Pretty.breaks) (
            map (fn (f, e) =>
              Pretty.block [Pretty.str (ml_label_uniq f ^ " = "), ml_from_iexpr NOBR e]) fs
          )
      | ml_from_iexpr br (ILookup (ls, v)) =
          brackify (eval_br br BR) [
            Pretty.str "(",
            ls |> map ((fn s => "#" ^ s) o ml_label_uniq) |> foldr1 (fn (l, e) => l ^ " o " ^ e) |> Pretty.str,
            Pretty.str ")",
            Pretty.str " ",
            Pretty.str v
          ]
    and mk_app_p br p args =
      brackify (eval_br br BR)
        (p :: map (ml_from_iexpr BR) args)
    and ml_from_app br ("Nil", []) =
          Pretty.str "[]"
      | ml_from_app br ("True", []) =
          Pretty.str "true"
      | ml_from_app br ("False", []) =
          Pretty.str "false"
      | ml_from_app br ("primeq", [e1, e2]) =
          brackify (eval_br br (INFX (4, L))) [
            ml_from_iexpr (INFX (4, L)) e1,
            Pretty.str "=",
            ml_from_iexpr (INFX (4, X)) e2
          ]
      | ml_from_app br ("Pair", [e1, e2]) =
          Pretty.list "(" ")" [
            ml_from_iexpr NOBR e1,
            ml_from_iexpr NOBR e2
          ]
      | ml_from_app br ("and", [e1, e2]) =
          brackify (eval_br br (INFX (~1, L))) [
            ml_from_iexpr (INFX (~1, L)) e1,
            Pretty.str "andalso",
            ml_from_iexpr (INFX (~1, X)) e2
          ]
      | ml_from_app br ("or", [e1, e2]) =
          brackify (eval_br br (INFX (~2, L))) [
            ml_from_iexpr (INFX (~2, L)) e1,
            Pretty.str "orelse",
            ml_from_iexpr (INFX (~2, X)) e2
          ]
      | ml_from_app br ("if", [b, e1, e2]) =
          brackify (eval_br br BR) [
            Pretty.str "if",
            ml_from_iexpr BR b,
            Pretty.str "then",
            ml_from_iexpr BR e1,
            Pretty.str "else",
            ml_from_iexpr BR e2
          ]
      | ml_from_app br ("add", [e1, e2]) =
          brackify (eval_br br (INFX (6, L))) [
            ml_from_iexpr (INFX (6, L)) e1,
            Pretty.str "+",
            ml_from_iexpr (INFX (6, X)) e2
          ]
      | ml_from_app br ("mult", [e1, e2]) =
          brackify (eval_br br (INFX (7, L))) [
            ml_from_iexpr (INFX (7, L)) e1,
            Pretty.str "+",
            ml_from_iexpr (INFX (7, X)) e2
          ]
      | ml_from_app br ("lt", [e1, e2]) =
          brackify (eval_br br (INFX (4, L))) [
            ml_from_iexpr (INFX (4, L)) e1,
            Pretty.str "<",
            ml_from_iexpr (INFX (4, X)) e2
          ]
      | ml_from_app br ("le", [e1, e2]) =
          brackify (eval_br br (INFX (7, L))) [
            ml_from_iexpr (INFX (4, L)) e1,
            Pretty.str "<=",
            ml_from_iexpr (INFX (4, X)) e2
          ]
      | ml_from_app br ("minus", es) =
          mk_app_p br (Pretty.str "~") es
      | ml_from_app br ("wfrec", es) =
          mk_app_p br (Pretty.str "wfrec") es
      | ml_from_app br (f, es) =
          let
            val args = map (ml_from_iexpr BR) es
            val brackify' = K (eval_br br BR) ? (single #> Pretty.enclose "(" ")")
            fun prepend_abs v body =
              Pretty.block [Pretty.str ("fn " ^ v ^ " =>"), Pretty.brk 1, body]
          in
            case sconst f args (ml_from_iexpr BR)
             of NONE =>
                  brackify (eval_br br BR) (Pretty.str (resolv f) :: args)
              | SOME ([], p) =>
                  brackify' p
              | SOME (vars, p) =>
                  p 
                  |> fold_rev prepend_abs vars
                  |> brackify'
          end;
    fun ml_from_funs (ds as d::ds_tl) =
      let
        fun mk_definer [] = "val"
          | mk_definer _ = "fun"
        fun check_args (_, Fun ((pats, _)::_, _)) NONE =
              SOME (mk_definer pats)
          | check_args (_, Fun ((pats, _)::_, _)) (SOME definer) =
              if mk_definer pats = definer
              then SOME definer
              else error ("Mixing simultaneous vals and funs not implemented")
          | check_args _ _ =
              error ("Function definition block containing other definitions than functions")
        val definer = the (fold check_args ds NONE);
        fun mk_eq definer f' ty (pats, expr) =
          let
            val lhs = [Pretty.str (definer ^ " " ^ f')]
                       @ (if null pats
                          then [Pretty.str ":", ml_from_typ NOBR ty]
                          else map (ml_from_pat BR) pats)
            val rhs = [Pretty.str "=", ml_from_iexpr NOBR expr]
          in
            Pretty.block (separate (Pretty.brk 1) (lhs @ rhs))
          end
        fun mk_fun definer (f, Fun (eqs as eq::eq_tl, (_, ty))) =
          let
            val (pats_hd::pats_tl) = (fst o split_list) eqs
            val _ = fold (fn x => fn y => (x ~~ y; y)) pats_tl pats_hd
              (*check for equal length of argument lists*)
          in (Pretty.block o Pretty.fbreaks) (
               (*Pretty.block [
                 Pretty.brk 1,
                 Pretty.str ": ",
                 ml_from_typ NOBR ty
               ]*)
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
    fun ml_from_datatypes ds =
      let
        val _ = debug 9 (fn _ => map (pretty_def o snd) ds |> Pretty.chunks |> Pretty.output) ();
        fun check_typ_dup ty xs =
          if AList.defined (op =) xs ty
          then error ("double datatype definition: " ^ quote ty)
          else xs
        fun check_typ_miss ty xs =
          if AList.defined (op =) xs ty
          then xs
          else error ("missing datatype definition: " ^ quote ty)
        fun group (name, Datatype (vs, _, _)) ts =
              (map (fn (_, []) => () | _ => error "can't serialize sort constrained datatype declaration to ML") vs;
              ts
              |> apsnd (check_typ_dup name)
              |> apsnd (AList.update (op =) (name, (vs, []))))
          | group (_, Datatypecons (_, _::_::_)) _ =
              error ("Datatype constructor containing more than one parameter")
          | group (name, Datatypecons (ty, tys)) ts =
              ts
              |> apfst (AList.default (op =) (resolv ty, []))
              |> apfst (AList.map_entry (op =) (resolv ty) (cons (name, tys)))
          | group _ _ =
              error ("Datatype block containing other statements than datatype or constructor definitions")
        fun group_cons (ty, co) ts =
          ts
          |> check_typ_miss ty
          |> AList.map_entry (op =) ty (rpair co o fst)
        fun mk_datatypes (ds as d::ds_tl) =
          let
            fun mk_cons (co, typs) =
              (Pretty.block oo praetify)
                (map (ml_from_typ NOBR) typs)
                (Pretty.str (resolv co))
            fun mk_datatype definer (t, (vs, cs)) =
              Pretty.block (
                [Pretty.str definer]
                @ postify (map (ml_from_typ BR o IVarT) vs)
                    (Pretty.str t)
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
        ([], [])
        |> fold group ds
        |-> (fn cons => fold group_cons cons)
        |> mk_datatypes
      end;
    fun ml_from_def (name, Typesyn (vs, ty)) =
        (map (fn (vname, []) => () | _ => error "can't serialize sort constrained type declaration to ML") vs;
         Pretty.block (
          Pretty.str "type "
          :: postify (map (Pretty.str o fst) vs) (Pretty.str name)
          @ [Pretty.str " =",
          Pretty.brk 1,
          ml_from_typ NOBR ty,
          Pretty.str ";"
        ]))
      | ml_from_def (name, Nop) =
          if exists (fn query => (is_some o query) name)
            [(fn name => styco name [] (ml_from_typ NOBR)),
             (fn name => sconst name [] (ml_from_iexpr NOBR))]
          then Pretty.str ""
          else error ("empty statement during serialization: " ^ quote name)
      | ml_from_def (name, Class _) =
          error ("can't serialize class declaration " ^ quote name ^ " to ML")
      | ml_from_def (name, Classinst _) =
          error ("can't serialize instance declaration " ^ quote name ^ " to ML")
  in case (snd o hd) ds
   of Fun _ => ml_from_funs ds
    | Datatypecons _ => ml_from_datatypes ds
    | Datatype _ => ml_from_datatypes ds
    | _ => (case ds of [d] => ml_from_def d)
  end;

in

fun ml_from_thingol nspgrp name_root styco sconst prims select module =
  let
    fun ml_from_module (name, ps) =
      Pretty.chunks ([
        Pretty.str ("structure " ^ name ^ " = "),
        Pretty.str "struct",
        Pretty.str ""
      ] @ ps @ [
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
              (case sconst s [] (K (Pretty.str ""))
               of NONE => 0
                | SOME (xs, _) => length xs)
          else 0
  in 
    module
    |> debug 5 (Pretty.output o pretty_module)
    |> debug 3 (fn _ => "connecting datatypes and classdecls...")
    |> connect_datatypes_clsdecls
    |> debug 3 (fn _ => "selecting submodule...")
    |> (if is_some select then (partof o the) select else I)
    |> debug 3 (fn _ => "eta-expanding...")
    |> eta_expand eta_expander
    |> debug 5 (Pretty.output o pretty_module)
    |> debug 3 (fn _ => "tupelizing datatypes...")
    |> tupelize_cons
    |> debug 3 (fn _ => "eliminating classes...")
    |> eliminate_classes
    |> debug 3 (fn _ => "generating...")
    |> serialize (ml_from_defs styco sconst) ml_from_module (ml_validator prims) nspgrp name_root
  end;

(* ML infix precedence
   7 / * div mod
   6 + - ^
   5 :: @
   4 = <> < > <= >=
   3 := o *)

end; (* local *)

end; (* struct *)

