(*  Title:      Pure/Syntax/mixfix.ML
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

Mixfix declarations, infixes, binders. Part of the Pure syntax.
*)

signature MIXFIX0 =
sig
  datatype mixfix =
    NoSyn |
    Mixfix of string * int list * int |
    Delimfix of string |
    Infixl of int |
    Infixr of int |
    Binder of string * int * int
  val max_pri: int
end;

signature MIXFIX1 =
sig
  include MIXFIX0
  val type_name: string -> mixfix -> string
  val const_name: string -> mixfix -> string
  val pure_types: (string * int * mixfix) list
  val pure_syntax: (string * string * mixfix) list
end;

signature MIXFIX =
sig
  include MIXFIX1
  structure SynExt: SYN_EXT
  local open SynExt in
    val syn_ext_types: string list -> (string * int * mixfix) list -> syn_ext
    val syn_ext_consts: string list -> (string * typ * mixfix) list -> syn_ext
  end
end;

functor MixfixFun(structure Lexicon: LEXICON and SynExt: SYN_EXT
  and SynTrans: SYN_TRANS): MIXFIX =
struct

structure SynExt = SynExt;
open Lexicon SynExt SynExt.Ast SynTrans;


(** mixfix declarations **)

datatype mixfix =
  NoSyn |
  Mixfix of string * int list * int |
  Delimfix of string |
  Infixl of int |
  Infixr of int |
  Binder of string * int * int;


(* type / const names *)

fun strip ("'" :: c :: cs) = c :: strip cs
  | strip ["'"] = []
  | strip (c :: cs) = c :: strip cs
  | strip [] = [];

val strip_esc = implode o strip o explode;


fun type_name t (Infixl _) = strip_esc t
  | type_name t (Infixr _) = strip_esc t
  | type_name t _ = t;

fun infix_name c = "op " ^ strip_esc c;

fun const_name c (Infixl _) = infix_name c
  | const_name c (Infixr _) = infix_name c
  | const_name c _ = c;


(* syn_ext_types *)

fun syn_ext_types logtypes type_decls =
  let
    fun name_of (t, _, mx) = type_name t mx;

    fun mk_infix t p1 p2 p3 =
      Mfix ("(_ " ^ t ^ "/ _)", [typeT, typeT] ---> typeT,
        strip_esc t, [p1, p2], p3);

    fun mfix_of (_, _, NoSyn) = None
      | mfix_of (t, 2, Infixl p) = Some (mk_infix t p (p + 1) p)
      | mfix_of (t, 2, Infixr p) = Some (mk_infix t (p + 1) p p)
      | mfix_of decl = error ("Bad mixfix declaration for type " ^
          quote (name_of decl));

    val mfix = mapfilter mfix_of type_decls;
    val xconsts = map name_of type_decls;
  in
    syn_ext logtypes mfix xconsts ([], [], [], []) ([], [])
  end;


(* syn_ext_consts *)

fun syn_ext_consts logtypes const_decls =
  let
    fun name_of (c, _, mx) = const_name c mx;

    fun mk_infix sy ty c p1 p2 p3 =
      [Mfix ("(_ " ^ sy ^ "/ _)", ty, c, [p1, p2], p3),
       Mfix ("op " ^ sy, ty, c, [], max_pri)];

    fun binder_typ _ (Type ("fun", [Type ("fun", [_, ty2]), ty3])) =
          [Type ("idts", []), ty2] ---> ty3
      | binder_typ c _ = error ("Bad type of binder " ^ quote c);

    fun mfix_of (_, _, NoSyn) = []
      | mfix_of (c, ty, Mixfix (sy, ps, p)) = [Mfix (sy, ty, c, ps, p)]
      | mfix_of (c, ty, Delimfix sy) = [Mfix (sy, ty, c, [], max_pri)]
      | mfix_of (sy, ty, Infixl p) = mk_infix sy ty (infix_name sy) p (p + 1) p
      | mfix_of (sy, ty, Infixr p) = mk_infix sy ty (infix_name sy) (p + 1) p p
      | mfix_of (c, ty, Binder (sy, p, q)) =
          [Mfix ("(3" ^ sy ^ "_./ _)", binder_typ c ty, sy, [0, p], q)];

    fun binder (c, _, Binder (sy, _, _)) = Some (sy, c)
      | binder _ = None;

    val mfix = flat (map mfix_of const_decls);
    val xconsts = map name_of const_decls;
    val binders = mapfilter binder const_decls;
    val binder_trs = map mk_binder_tr binders;
    val binder_trs' = map (mk_binder_tr' o swap) binders;
  in
    syn_ext logtypes mfix xconsts ([], binder_trs, binder_trs', []) ([], [])
  end;



(** Pure syntax **)

val pure_types =
  map (fn t => (t, 0, NoSyn))
    (terminals @ [logic, "type", "types", "sort", "classes", args,
      "idt", "idts", "aprop", "asms", any, sprop]);

val pure_syntax =
 [("_lambda",   "[idts, 'a] => logic",            Mixfix ("(3%_./ _)", [], 0)),
  ("_abs",      "'a",                             NoSyn),
  ("",          "'a => " ^ args,                  Delimfix "_"),
  ("_args",     "['a, " ^ args ^ "] => " ^ args,  Delimfix "_,/ _"),
  ("",          "id => idt",                      Delimfix "_"),
  ("_idtyp",    "[id, type] => idt",              Mixfix ("_::_", [], 0)),
  ("",          "idt => idt",                     Delimfix "'(_')"),
  ("",          "idt => idts",                    Delimfix "_"),
  ("_idts",     "[idt, idts] => idts",            Mixfix ("_/ _", [1, 0], 0)),
  ("",          "id => aprop",                    Delimfix "_"),
  ("",          "var => aprop",                   Delimfix "_"),
  ("_aprop",    "aprop => prop",                  Delimfix "PROP _"),
  ("",          "prop => asms",                   Delimfix "_"),
  ("_asms",     "[prop, asms] => asms",           Delimfix "_;/ _"),
  ("_bigimpl",  "[asms, prop] => prop",           Mixfix ("((3[| _ |]) ==>/ _)", [0, 1], 1)),
  ("_ofclass",  "[type, logic] => prop",          Delimfix "(1OFCLASS/(1'(_,/ _')))"),
  ("_K",        "'a",                             NoSyn),
  ("",          "id => logic",                    Delimfix "_"),
  ("",          "var => logic",                   Delimfix "_")]

end;
