(*  Title:      Pure/Syntax/mixfix.ML
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

Mixfix declarations, infixes, binders. Also parts of the Pure syntax.
*)

signature MIXFIX0 =
sig
  datatype mixfix =
    NoSyn |
    Mixfix of string * int list * int |
    Delimfix of string |
    InfixlName of string * int |
    InfixrName of string * int |
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
  val pure_appl_syntax: (string * string * mixfix) list
  val pure_applC_syntax: (string * string * mixfix) list
  val pure_sym_syntax: (string * string * mixfix) list
end;

signature MIXFIX =
sig
  include MIXFIX1
  val syn_ext_types: string list -> (string * int * mixfix) list
    -> SynExt.syn_ext
  val syn_ext_consts: string list -> (string * typ * mixfix) list
    -> SynExt.syn_ext
end;


structure Mixfix : MIXFIX =
struct

open Lexicon SynExt Ast SynTrans;


(** mixfix declarations **)

datatype mixfix =
  NoSyn |
  Mixfix of string * int list * int |
  Delimfix of string |
  InfixlName of string * int |
  InfixrName of string * int |
  Infixl of int |
  Infixr of int |
  Binder of string * int * int;


(* type / const names *)

fun strip ("'" :: c :: cs) = c :: strip cs
  | strip ["'"] = []
  | strip (c :: cs) = c :: strip cs
  | strip [] = [];

val strip_esc = implode o strip o explode;

fun type_name t (InfixlName _) = t
  | type_name t (InfixrName _) = t
  | type_name t (Infixl _) = strip_esc t
  | type_name t (Infixr _) = strip_esc t
  | type_name t _ = t;

fun const_name c (InfixlName _) = c
  | const_name c (InfixrName _) = c
  | const_name c (Infixl _) = "op " ^ strip_esc c
  | const_name c (Infixr _) = "op " ^ strip_esc c
  | const_name c _ = c;


(* syn_ext_types *)

fun syn_ext_types logtypes type_decls =
  let
    fun name_of (t, _, mx) = type_name t mx;

    fun mk_infix sy t p1 p2 p3 =
      Mfix ("(_ " ^ sy ^ "/ _)", [typeT, typeT] ---> typeT, t, [p1, p2], p3);

    fun mfix_of decl =
      let val t = name_of decl in
        (case decl of
          (_, _, NoSyn) => None
        | (_, 2, InfixlName (sy, p)) => Some (mk_infix t sy p (p + 1) p)
        | (_, 2, InfixrName (sy, p)) => Some (mk_infix t sy (p + 1) p p)
        | (sy, 2, Infixl p) => Some (mk_infix t sy p (p + 1) p)
        | (sy, 2, Infixr p) => Some (mk_infix t sy (p + 1) p p)
        | _ => error ("Bad mixfix declaration for type " ^ quote t))
      end;

    val mfix = mapfilter mfix_of type_decls;
    val xconsts = map name_of type_decls;
  in
    syn_ext logtypes mfix xconsts ([], [], [], []) [] ([], [])
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

    fun mfix_of decl =
      let val c = name_of decl in
        (case decl of
          (_, _, NoSyn) => []
        | (_, ty, Mixfix (sy, ps, p)) => [Mfix (sy, ty, c, ps, p)]
        | (_, ty, Delimfix sy) => [Mfix (sy, ty, c, [], max_pri)]
        | (_, ty, InfixlName (sy, p)) => mk_infix sy ty c p (p + 1) p
        | (_, ty, InfixrName (sy, p)) => mk_infix sy ty c (p + 1) p p
        | (sy, ty, Infixl p) => mk_infix sy ty c p (p + 1) p
        | (sy, ty, Infixr p) => mk_infix sy ty c (p + 1) p p
        | (_, ty, Binder (sy, p, q)) =>
            [Mfix ("(3" ^ sy ^ "_./ _)", binder_typ c ty, sy, [0, p], q)])
    end;

    fun binder (c, _, Binder (sy, _, _)) = Some (sy, c)
      | binder _ = None;

    val mfix = flat (map mfix_of const_decls);
    val xconsts = map name_of const_decls;
    val binders = mapfilter binder const_decls;
    val binder_trs = map mk_binder_tr binders;
    val binder_trs' = map (apsnd fix_tr' o mk_binder_tr' o swap) binders;
  in
    syn_ext logtypes mfix xconsts ([], binder_trs, binder_trs', []) [] ([], [])
  end;



(** Pure syntax **)

val pure_types =
  map (fn t => (t, 0, NoSyn))
    (terminals @ [logic, "type", "types", "sort", "classes", args, cargs,
      "pttrn", "idt", "idts", "aprop", "asms", any, sprop, "dummy"]);

val pure_syntax =
 [("_lambda",      "[idts, 'a] => logic",           Mixfix ("(3%_./ _)", [], 0)),
  ("_abs",         "'a",                            NoSyn),
  ("",             "'a => " ^ args,                 Delimfix "_"),
  ("_args",        "['a, " ^ args ^ "] => " ^ args, Delimfix "_,/ _"),
  ("",             "id => idt",                     Delimfix "_"),
  ("_idtyp",       "[id, type] => idt",             Mixfix ("_::_", [], 0)),
  ("",             "idt => idt",                    Delimfix "'(_')"),
  ("",             "idt => pttrn",                  Delimfix "_"),
  ("",             "pttrn => idts",                 Delimfix "_"),
  ("_idts",        "[pttrn, idts] => idts",         Mixfix ("_/ _", [1, 0], 0)),
  ("",             "id => aprop",                   Delimfix "_"),
  ("",             "var => aprop",                  Delimfix "_"),
  ("_aprop",       "aprop => prop",                 Delimfix "PROP _"),
  ("",             "prop => asms",                  Delimfix "_"),
  ("_asms",        "[prop, asms] => asms",          Delimfix "_;/ _"),
  ("_bigimpl",     "[asms, prop] => prop",          Mixfix ("((3[| _ |])/ ==> _)", [0, 1], 1)),
  ("_ofclass",     "[type, logic] => prop",         Delimfix "(1OFCLASS/(1'(_,/ _')))"),
  ("_mk_ofclass",  "_",                             NoSyn),
  ("_mk_ofclassS", "_",                             NoSyn),
  ("_K",           "_",                             NoSyn),
  ("",             "id => logic",                   Delimfix "_"),
  ("",             "var => logic",                  Delimfix "_")];

val pure_appl_syntax =
 [("_appl", "[('b => 'a), args] => logic", Mixfix ("(1_/(1'(_')))", [max_pri, 0], max_pri)),
  ("_appl", "[('b => 'a), args] => aprop", Mixfix ("(1_/(1'(_')))", [max_pri, 0], max_pri))];

val pure_applC_syntax =
 [("",       "'a => cargs",                  Delimfix "_"),
  ("_cargs", "['a, cargs] => cargs",         Mixfix ("_/ _", [max_pri, max_pri], max_pri)),
  ("_applC", "[('b => 'a), cargs] => logic", Mixfix ("(1_/ _)", [max_pri, max_pri], max_pri - 1)),
  ("_applC", "[('b => 'a), cargs] => aprop", Mixfix ("(1_/ _)", [max_pri, max_pri], max_pri - 1))];

val pure_sym_syntax =
 [("fun",      "[type, type] => type",  Mixfix ("(_/ \\<Rightarrow> _)", [1, 0], 0)),
  ("_bracket", "[types, type] => type", Mixfix ("([_]/ \\<Rightarrow> _)", [0, 0], 0)),
  ("_lambda",  "[idts, 'a] => logic",   Mixfix ("(3\\<lambda>_./ _)", [], 0)),
  ("==>",      "[prop, prop] => prop",  InfixrName ("\\<Midarrow>\\<Rightarrow>", 1)),
  ("_bigimpl", "[asms, prop] => prop",  Mixfix ("((3\\<lbrakk>_\\<rbrakk>)/ \\<Midarrow>\\<Rightarrow> _)", [0, 1], 1)),
  ("==",       "['a::{}, 'a] => prop",  InfixrName ("\\<equiv>", 2)),
  ("!!",       "[idts, prop] => prop",  Mixfix ("(3\\<And>_./ _)", [0, 0], 0))];

end;
