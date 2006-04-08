(*  Title:      Pure/Syntax/mixfix.ML
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

Mixfix declarations, infixes, binders.
*)

signature MIXFIX0 =
sig
  datatype mixfix =
    NoSyn |
    Mixfix of string * int list * int |
    Delimfix of string |
    InfixName of string * int |
    InfixlName of string * int |
    InfixrName of string * int |
    Infix of int |    (*obsolete*)
    Infixl of int |   (*obsolete*)
    Infixr of int |   (*obsolete*)
    Binder of string * int * int |
    Structure
end;

signature MIXFIX1 =
sig
  include MIXFIX0
  val literal: string -> mixfix
  val no_syn: 'a * 'b -> 'a * 'b * mixfix
  val pretty_mixfix: mixfix -> Pretty.T
  val type_name: string -> mixfix -> string
  val const_name: string -> mixfix -> string
  val const_mixfix: string -> mixfix -> string * mixfix
  val mixfix_const: string -> mixfix -> string * bool
  val unlocalize_mixfix: mixfix -> mixfix
  val mixfix_args: mixfix -> int
  val mixfix_content: mixfix -> string list list
end;

signature MIXFIX =
sig
  include MIXFIX1
  val syn_ext_types: (string * int * mixfix) list -> SynExt.syn_ext
  val syn_ext_consts: (string -> bool) -> (string * typ * mixfix) list -> SynExt.syn_ext
end;

structure Mixfix: MIXFIX =
struct


(** mixfix declarations **)

datatype mixfix =
  NoSyn |
  Mixfix of string * int list * int |
  Delimfix of string |
  InfixName of string * int |
  InfixlName of string * int |
  InfixrName of string * int |
  Infix of int |      (*obsolete*)
  Infixl of int |     (*obsolete*)
  Infixr of int |     (*obsolete*)
  Binder of string * int * int |
  Structure;

val literal = Delimfix o SynExt.escape_mfix;

fun no_syn (x, y) = (x, y, NoSyn);


(* pretty_mixfix *)

local

val quoted = Pretty.quote o Pretty.str;
val keyword = Pretty.keyword;
val parens = Pretty.enclose "(" ")";
val brackets = Pretty.enclose "[" "]";
val int = Pretty.str o string_of_int;

in

fun pretty_mixfix NoSyn = Pretty.str ""
  | pretty_mixfix (Mixfix (s, ps, p)) =
      parens (Pretty.breaks [quoted s, brackets (Pretty.commas (map int ps)), int p])
  | pretty_mixfix (Delimfix s) = parens [quoted s]
  | pretty_mixfix (InfixName (s, p)) = parens (Pretty.breaks [keyword "infix", quoted s, int p])
  | pretty_mixfix (InfixlName (s, p)) = parens (Pretty.breaks [keyword "infixl", quoted s, int p])
  | pretty_mixfix (InfixrName (s, p)) = parens (Pretty.breaks [keyword "infixl", quoted s, int p])
  | pretty_mixfix (Infix p) = parens (Pretty.breaks [keyword "infix", int p])
  | pretty_mixfix (Infixl p) = parens (Pretty.breaks [keyword "infixl", int p])
  | pretty_mixfix (Infixr p) = parens (Pretty.breaks [keyword "infixr", int p])
  | pretty_mixfix (Binder (s, p1, p2)) =
      parens (Pretty.breaks [keyword "binder", quoted s, brackets [int p1], int p2])
  | pretty_mixfix Structure = parens [keyword "structure"];

end;


(* syntax specifications *)

fun strip ("'" :: c :: cs) = c :: strip cs
  | strip ["'"] = []
  | strip (c :: cs) = c :: strip cs
  | strip [] = [];

val strip_esc = implode o strip o Symbol.explode;

fun deprecated c = (warning ("Unnamed infix operator " ^ quote c ^ " -- deprecated"); c);

fun type_name t (InfixName _) = t
  | type_name t (InfixlName _) = t
  | type_name t (InfixrName _) = t
  | type_name t (Infix _) = deprecated (strip_esc t)
  | type_name t (Infixl _) = deprecated (strip_esc t)
  | type_name t (Infixr _) = deprecated (strip_esc t)
  | type_name t _ = t;

fun const_name c (InfixName _) = c
  | const_name c (InfixlName _) = c
  | const_name c (InfixrName _) = c
  | const_name c (Infix _) = "op " ^ deprecated (strip_esc c)
  | const_name c (Infixl _) = "op " ^ deprecated (strip_esc c)
  | const_name c (Infixr _) = "op " ^ deprecated (strip_esc c)
  | const_name c _ = c;

fun fix_mixfix c (Infix p) = InfixName (c, p)
  | fix_mixfix c (Infixl p) = InfixlName (c, p)
  | fix_mixfix c (Infixr p) = InfixrName (c, p)
  | fix_mixfix _ mx = mx;

fun const_mixfix c mx = (const_name c mx, fix_mixfix c mx);

fun mixfix_const c NoSyn = (c, true)
  | mixfix_const c _ = (Lexicon.constN ^ c, false);

fun map_mixfix _ NoSyn = NoSyn
  | map_mixfix f (Mixfix (sy, ps, p)) = Mixfix (f sy, ps, p)
  | map_mixfix f (Delimfix sy) = Delimfix (f sy)
  | map_mixfix f (InfixName (sy, p)) = InfixName (f sy, p)
  | map_mixfix f (InfixlName (sy, p)) = InfixlName (f sy, p)
  | map_mixfix f (InfixrName (sy, p)) = InfixrName (f sy, p)
  | map_mixfix f (Binder (sy, p, q)) = Binder (f sy, p, q)
  | map_mixfix _ Structure = Structure
  | map_mixfix _ _ = raise Fail ("map_mixfix: illegal occurrence of unnamed infix");

val unlocalize_mixfix = map_mixfix SynExt.unlocalize_mfix;

fun mixfix_args NoSyn = 0
  | mixfix_args (Mixfix (sy, _, _)) = SynExt.mfix_args sy
  | mixfix_args (Delimfix sy) = SynExt.mfix_args sy
  | mixfix_args (InfixName (sy, _)) = 2 + SynExt.mfix_args sy
  | mixfix_args (InfixlName (sy, _)) = 2 + SynExt.mfix_args sy
  | mixfix_args (InfixrName (sy, _)) = 2 + SynExt.mfix_args sy
  | mixfix_args (Infix _) = 2
  | mixfix_args (Infixl _) = 2
  | mixfix_args (Infixr _) = 2
  | mixfix_args (Binder _) = 1
  | mixfix_args Structure = 0;


(* syn_ext_types *)

fun syn_ext_types type_decls =
  let
    fun name_of (t, _, mx) = type_name t mx;

    fun mk_infix sy t p1 p2 p3 =
      SynExt.Mfix ("(_ " ^ sy ^ "/ _)",
        [SynExt.typeT, SynExt.typeT] ---> SynExt.typeT, t, [p1, p2], p3);

    fun mfix_of decl =
      let val t = name_of decl in
        (case decl of
          (_, _, NoSyn) => NONE
        | (_, 2, InfixName (sy, p)) => SOME (mk_infix sy t (p + 1) (p + 1) p)
        | (_, 2, InfixlName (sy, p)) => SOME (mk_infix sy t p (p + 1) p)
        | (_, 2, InfixrName (sy, p)) => SOME (mk_infix sy t (p + 1) p p)
        | (sy, 2, Infix p) => SOME (mk_infix sy t (p + 1) (p + 1) p)
        | (sy, 2, Infixl p) => SOME (mk_infix sy t p (p + 1) p)
        | (sy, 2, Infixr p) => SOME (mk_infix sy t (p + 1) p p)
        | _ => error ("Bad mixfix declaration for type: " ^ quote t))
      end;

    val mfix = List.mapPartial mfix_of type_decls;
    val xconsts = map name_of type_decls;
  in SynExt.syn_ext mfix xconsts ([], [], [], []) [] ([], []) end;


(* syn_ext_consts *)

val binder_stamp = stamp ();

fun syn_ext_consts is_logtype const_decls =
  let
    fun name_of (c, _, mx) = const_name c mx;

    fun mk_infix sy ty c p1 p2 p3 =
      [SynExt.Mfix ("op " ^ sy, ty, c, [], SynExt.max_pri),
       SynExt.Mfix ("(_ " ^ sy ^ "/ _)", ty, c, [p1, p2], p3)];

    fun binder_typ _ (Type ("fun", [Type ("fun", [_, ty2]), ty3])) =
          [Type ("idts", []), ty2] ---> ty3
      | binder_typ c _ = error ("Bad type of binder: " ^ quote c);

    fun mfix_of decl =
      let val c = name_of decl in
        (case decl of
          (_, _, NoSyn) => []
        | (_, ty, Mixfix (sy, ps, p)) => [SynExt.Mfix (sy, ty, c, ps, p)]
        | (_, ty, Delimfix sy) => [SynExt.Mfix (sy, ty, c, [], SynExt.max_pri)]
        | (_, ty, InfixName (sy, p)) => mk_infix sy ty c (p + 1) (p + 1) p
        | (_, ty, InfixlName (sy, p)) => mk_infix sy ty c p (p + 1) p
        | (_, ty, InfixrName (sy, p)) => mk_infix sy ty c (p + 1) p p
        | (sy, ty, Infix p) => mk_infix sy ty c (p + 1) (p + 1) p
        | (sy, ty, Infixl p) => mk_infix sy ty c p (p + 1) p
        | (sy, ty, Infixr p) => mk_infix sy ty c (p + 1) p p
        | (_, ty, Binder (sy, p, q)) =>
            [SynExt.Mfix ("(3" ^ sy ^ "_./ _)", binder_typ c ty, sy, [0, p], q)]
        | _ => error ("Bad mixfix declaration for const: " ^ quote c))
    end;

    fun binder (c, _, Binder (sy, _, _)) = SOME (sy, c)
      | binder _ = NONE;

    val mfix = List.concat (map mfix_of const_decls);
    val xconsts = map name_of const_decls;
    val binders = List.mapPartial binder const_decls;
    val binder_trs = binders |> map (SynExt.stamp_trfun binder_stamp o
        apsnd K o SynTrans.mk_binder_tr);
    val binder_trs' = binders |> map (SynExt.stamp_trfun binder_stamp o
        apsnd (K o SynTrans.non_typed_tr') o SynTrans.mk_binder_tr' o swap);
  in
    SynExt.syn_ext' true is_logtype
      mfix xconsts ([], binder_trs, binder_trs', []) [] ([], [])
  end;

fun mixfix_content mx =
  let
    fun delims sy = SynExt.mfix_delims sy;
    fun op_delims sy = let val ds = delims sy in ["op" :: ds, ds] end;
  in
    case mx of
      Mixfix (sy, _, _) => [delims sy]
    | Delimfix sy => [delims sy]
    | InfixName (sy, _) => op_delims sy
    | InfixlName (sy, _) => op_delims sy
    | InfixrName (sy, _) => op_delims sy
    | Binder (sy, _, _) => [delims sy @ ["."]]
    | _ => []
  end;

end;
