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
    InfixName of string * int |
    InfixlName of string * int |
    InfixrName of string * int |
    Infix of int |
    Infixl of int |
    Infixr of int |
    Binder of string * int * int
end;

signature MIXFIX1 =
sig
  include MIXFIX0
  val no_syn: 'a * 'b -> 'a * 'b * mixfix
  val type_name: string -> mixfix -> string
  val const_name: string -> mixfix -> string
  val fix_mixfix: string -> mixfix -> mixfix
  val mixfix_args: mixfix -> int
  val pure_nonterms: string list
  val pure_syntax: (string * string * mixfix) list
  val pure_appl_syntax: (string * string * mixfix) list
  val pure_applC_syntax: (string * string * mixfix) list
  val pure_sym_syntax:  (string * string * mixfix) list
  val pure_xsym_syntax: (string * string * mixfix) list
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


(** mixfix declarations **)

datatype mixfix =
  NoSyn |
  Mixfix of string * int list * int |
  Delimfix of string |
  InfixName of string * int |
  InfixlName of string * int |
  InfixrName of string * int |
  Infix of int |
  Infixl of int |
  Infixr of int |
  Binder of string * int * int;

fun no_syn (x, y) = (x, y, NoSyn);


(* type / const names *)

fun strip ("'" :: c :: cs) = c :: strip cs
  | strip ["'"] = []
  | strip (c :: cs) = c :: strip cs
  | strip [] = [];

val strip_esc = implode o strip o Symbol.explode;

fun type_name t (InfixName _) = t
  | type_name t (InfixlName _) = t
  | type_name t (InfixrName _) = t
  | type_name t (Infix _) = strip_esc t
  | type_name t (Infixl _) = strip_esc t
  | type_name t (Infixr _) = strip_esc t
  | type_name t _ = t;

fun const_name c (InfixName _) = c
  | const_name c (InfixlName _) = c
  | const_name c (InfixrName _) = c
  | const_name c (Infix _) = "op " ^ strip_esc c
  | const_name c (Infixl _) = "op " ^ strip_esc c
  | const_name c (Infixr _) = "op " ^ strip_esc c
  | const_name c _ = c;

fun fix_mixfix c (Infix p) = (InfixName (c, p))
  | fix_mixfix c (Infixl p) = (InfixlName (c, p))
  | fix_mixfix c (Infixr p) = (InfixrName (c, p))
  | fix_mixfix _ mx = mx;


(* mixfix_args *)

fun mixfix_args NoSyn = 0
  | mixfix_args (Mixfix (sy, _, _)) = SynExt.mfix_args sy
  | mixfix_args (Delimfix sy) = SynExt.mfix_args sy
  | mixfix_args (*infix or binder*) _ = 2;


(* syn_ext_types *)

fun syn_ext_types logtypes type_decls =
  let
    fun name_of (t, _, mx) = type_name t mx;

    fun mk_infix sy t p1 p2 p3 =
      SynExt.Mfix ("(_ " ^ sy ^ "/ _)",
        [SynExt.typeT, SynExt.typeT] ---> SynExt.typeT, t, [p1, p2], p3);

    fun mfix_of decl =
      let val t = name_of decl in
        (case decl of
          (_, _, NoSyn) => None
        | (_, 2, InfixName (sy, p)) => Some (mk_infix sy t (p + 1) (p + 1) p)
        | (_, 2, InfixlName (sy, p)) => Some (mk_infix sy t p (p + 1) p)
        | (_, 2, InfixrName (sy, p)) => Some (mk_infix sy t (p + 1) p p)
        | (sy, 2, Infix p) => Some (mk_infix sy t (p + 1) (p + 1) p)
        | (sy, 2, Infixl p) => Some (mk_infix sy t p (p + 1) p)
        | (sy, 2, Infixr p) => Some (mk_infix sy t (p + 1) p p)
        | _ => error ("Bad mixfix declaration for type " ^ quote t))
      end;

    val mfix = mapfilter mfix_of type_decls;
    val xconsts = map name_of type_decls;
  in SynExt.syn_ext logtypes mfix xconsts ([], [], [], []) [] ([], []) end;


(* syn_ext_consts *)

fun syn_ext_consts logtypes const_decls =
  let
    fun name_of (c, _, mx) = const_name c mx;

    fun mk_infix sy ty c p1 p2 p3 =
      [SynExt.Mfix ("op " ^ sy, ty, c, [], SynExt.max_pri),
       SynExt.Mfix ("(_ " ^ sy ^ "/ _)", ty, c, [p1, p2], p3)];

    fun binder_typ _ (Type ("fun", [Type ("fun", [_, ty2]), ty3])) =
          [Type ("idts", []), ty2] ---> ty3
      | binder_typ c _ = error ("Bad type of binder " ^ quote c);

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
            [SynExt.Mfix ("(3" ^ sy ^ "_./ _)", binder_typ c ty, sy, [0, p], q)])
    end;

    fun binder (c, _, Binder (sy, _, _)) = Some (sy, c)
      | binder _ = None;

    val mfix = flat (map mfix_of const_decls);
    val xconsts = map name_of const_decls;
    val binders = mapfilter binder const_decls;
    val binder_trs = map SynTrans.mk_binder_tr binders;
    val binder_trs' = map (apsnd SynExt.fix_tr' o SynTrans.mk_binder_tr' o swap) binders;
  in SynExt.syn_ext logtypes mfix xconsts ([], binder_trs, binder_trs', []) [] ([], []) end;



(** Pure syntax **)

val pure_nonterms =
  (Lexicon.terminals @ [SynExt.logic, "type", "types", "sort", "classes",
    SynExt.args, SynExt.cargs, "pttrn", "pttrns", "idt", "idts", "aprop",
    "asms", SynExt.any, SynExt.sprop]);

val pure_syntax =
 [("_lambda",      "[pttrns, 'a] => logic",         Mixfix ("(3%_./ _)", [0, 3], 3)),
  ("_abs",         "'a",                            NoSyn),
  ("",             "'a => " ^ SynExt.args,          Delimfix "_"),
  ("_args",        "['a, " ^ SynExt.args ^ "] => " ^ SynExt.args, Delimfix "_,/ _"),
  ("",             "id => idt",                     Delimfix "_"),
  ("_idtyp",       "[id, type] => idt",             Mixfix ("_::_", [], 0)),
  ("",             "idt => idt",                    Delimfix "'(_')"),
  ("",             "idt => idts",                   Delimfix "_"),
  ("_idts",        "[idt, idts] => idts",           Mixfix ("_/ _", [1, 0], 0)),
  ("",             "idt => pttrn",                  Delimfix "_"),
  ("",             "pttrn => pttrns",               Delimfix "_"),
  ("_pttrns",      "[pttrn, pttrns] => pttrns",     Mixfix ("_/ _", [1, 0], 0)),
  ("",             "id => aprop",                   Delimfix "_"),
  ("",             "longid => aprop",               Delimfix "_"),
  ("",             "var => aprop",                  Delimfix "_"),
  ("_DDDOT",       "aprop",                         Delimfix "..."),
  ("_aprop",       "aprop => prop",                 Delimfix "PROP _"),
  ("",             "prop => asms",                  Delimfix "_"),
  ("_asms",        "[prop, asms] => asms",          Delimfix "_;/ _"),
  ("_bigimpl",     "[asms, prop] => prop",          Mixfix ("((3[| _ |])/ ==> _)", [0, 1], 1)),
  ("_ofclass",     "[type, logic] => prop",         Delimfix "(1OFCLASS/(1'(_,/ _')))"),
  ("_mk_ofclass",  "_",                             NoSyn),
  ("_TYPE",        "type => logic",                 Delimfix "(1TYPE/(1'(_')))"),
  ("_K",           "_",                             NoSyn),
  ("",             "id => logic",                   Delimfix "_"),
  ("",             "longid => logic",               Delimfix "_"),
  ("",             "var => logic",                  Delimfix "_"),
  ("_DDDOT",       "logic",                         Delimfix "...")];

val pure_appl_syntax =
 [("_appl", "[('b => 'a), args] => logic", Mixfix ("(1_/(1'(_')))", [SynExt.max_pri, 0], SynExt.max_pri)),
  ("_appl", "[('b => 'a), args] => aprop", Mixfix ("(1_/(1'(_')))", [SynExt.max_pri, 0], SynExt.max_pri))];

val pure_applC_syntax =
 [("",       "'a => cargs",                  Delimfix "_"),
  ("_cargs", "['a, cargs] => cargs",         Mixfix ("_/ _", [SynExt.max_pri, SynExt.max_pri], SynExt.max_pri)),
  ("_applC", "[('b => 'a), cargs] => logic", Mixfix ("(1_/ _)", [SynExt.max_pri, SynExt.max_pri], SynExt.max_pri - 1)),
  ("_applC", "[('b => 'a), cargs] => aprop", Mixfix ("(1_/ _)", [SynExt.max_pri, SynExt.max_pri], SynExt.max_pri - 1))];

val pure_sym_syntax =
 [("fun",      "[type, type] => type",  Mixfix ("(_/ \\<Rightarrow> _)", [1, 0], 0)),
  ("_bracket", "[types, type] => type", Mixfix ("([_]/ \\<Rightarrow> _)", [0, 0], 0)),
  ("_ofsort",  "[tid, sort] => type",   Mixfix ("_\\<Colon>_", [SynExt.max_pri, 0], SynExt.max_pri)),
  ("_constrain", "['a, type] => 'a",    Mixfix ("_\\<Colon>_", [4, 0], 3)),
  ("_idtyp",   "[id, type] => idt",     Mixfix ("_\\<Colon>_", [], 0)),
  ("_lambda",  "[pttrns, 'a] => logic", Mixfix ("(3\\<lambda>_./ _)", [0, 3], 3)),
  ("==>",      "[prop, prop] => prop",  InfixrName ("\\<Midarrow>\\<Rightarrow>", 1)),
  ("_bigimpl", "[asms, prop] => prop",  Mixfix ("((3\\<lbrakk>_\\<rbrakk>)/ \\<Midarrow>\\<Rightarrow> _)", [0, 1], 1)),
  ("==",       "['a::{}, 'a] => prop",  InfixrName ("\\<equiv>", 2)),
  ("!!",       "[idts, prop] => prop",  Mixfix ("(3\\<And>_./ _)", [0, 0], 0))];

val pure_xsym_syntax =
 [("==>",      "[prop, prop] => prop",  InfixrName ("\\<Longrightarrow>", 1)),
  ("=?=",      "['a::{}, 'a] => prop",  InfixrName ("\\<equiv>\\<^sup>?", 2)),
  ("_DDDOT",   "aprop",                 Delimfix "\\<dots>"),
  ("_bigimpl", "[asms, prop] => prop",  Mixfix ("((3\\<lbrakk>_\\<rbrakk>)/ \\<Longrightarrow> _)", [0, 1], 1)),
  ("_DDDOT",   "logic",                 Delimfix "\\<dots>")];

end;
