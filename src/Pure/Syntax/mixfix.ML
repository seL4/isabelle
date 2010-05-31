(*  Title:      Pure/Syntax/mixfix.ML
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

Mixfix declarations, infixes, binders.
*)

signature MIXFIX0 =
sig
  datatype mixfix =
    NoSyn |
    Mixfix of string * int list * int |
    Delimfix of string |
    Infix of string * int |
    Infixl of string * int |
    Infixr of string * int |
    Binder of string * int * int |
    Structure
  val binder_name: string -> string
end;

signature MIXFIX1 =
sig
  include MIXFIX0
  val no_syn: 'a * 'b -> 'a * 'b * mixfix
  val pretty_mixfix: mixfix -> Pretty.T
  val mixfix_args: mixfix -> int
  val mixfixT: mixfix -> typ
  val make_type: int -> typ
end;

signature MIXFIX =
sig
  include MIXFIX1
  val syn_ext_types: (string * typ * mixfix) list -> Syn_Ext.syn_ext
  val syn_ext_consts: (string -> bool) -> (string * typ * mixfix) list -> Syn_Ext.syn_ext
end;

structure Mixfix: MIXFIX =
struct


(** mixfix declarations **)

datatype mixfix =
  NoSyn |
  Mixfix of string * int list * int |
  Delimfix of string |
  Infix of string * int |
  Infixl of string * int |
  Infixr of string * int |
  Binder of string * int * int |
  Structure;

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
  | pretty_mixfix (Infix (s, p)) = parens (Pretty.breaks [keyword "infix", quoted s, int p])
  | pretty_mixfix (Infixl (s, p)) = parens (Pretty.breaks [keyword "infixl", quoted s, int p])
  | pretty_mixfix (Infixr (s, p)) = parens (Pretty.breaks [keyword "infixl", quoted s, int p])
  | pretty_mixfix (Binder (s, p1, p2)) =
      parens (Pretty.breaks [keyword "binder", quoted s, brackets [int p1], int p2])
  | pretty_mixfix Structure = parens [keyword "structure"];

end;


(* syntax specifications *)

fun mixfix_args NoSyn = 0
  | mixfix_args (Mixfix (sy, _, _)) = Syn_Ext.mfix_args sy
  | mixfix_args (Delimfix sy) = Syn_Ext.mfix_args sy
  | mixfix_args (Infix (sy, _)) = 2 + Syn_Ext.mfix_args sy
  | mixfix_args (Infixl (sy, _)) = 2 + Syn_Ext.mfix_args sy
  | mixfix_args (Infixr (sy, _)) = 2 + Syn_Ext.mfix_args sy
  | mixfix_args (Binder _) = 1
  | mixfix_args Structure = 0;

fun mixfixT (Binder _) = (dummyT --> dummyT) --> dummyT
  | mixfixT mx = replicate (mixfix_args mx) dummyT ---> dummyT;


(* syn_ext_types *)

fun make_type n = replicate n Syn_Ext.typeT ---> Syn_Ext.typeT;

fun syn_ext_types type_decls =
  let
    fun mk_infix sy ty t p1 p2 p3 = Syn_Ext.Mfix ("(_ " ^ sy ^ "/ _)", ty, t, [p1, p2], p3);

    fun mfix_of (_, _, NoSyn) = NONE
      | mfix_of (t, ty, Mixfix (sy, ps, p)) = SOME (Syn_Ext.Mfix (sy, ty, t, ps, p))
      | mfix_of (t, ty, Delimfix sy) = SOME (Syn_Ext.Mfix (sy, ty, t, [], Syn_Ext.max_pri))
      | mfix_of (t, ty, Infix (sy, p)) = SOME (mk_infix sy ty t (p + 1) (p + 1) p)
      | mfix_of (t, ty, Infixl (sy, p)) = SOME (mk_infix sy ty t p (p + 1) p)
      | mfix_of (t, ty, Infixr (sy, p)) = SOME (mk_infix sy ty t (p + 1) p p)
      | mfix_of (t, _, _) = error ("Bad mixfix declaration for " ^ quote t);  (* FIXME printable t (!?) *)

    fun check_args (_, ty, _) (SOME (mfix as Syn_Ext.Mfix (sy, _, _, _, _))) =
          if length (Term.binder_types ty) = Syn_Ext.mfix_args sy then ()
          else Syn_Ext.err_in_mfix "Bad number of type constructor arguments" mfix
      | check_args _ NONE = ();

    val mfix = map mfix_of type_decls;
    val _ = map2 check_args type_decls mfix;
    val xconsts = map #1 type_decls;
  in Syn_Ext.syn_ext (map_filter I mfix) xconsts ([], [], [], []) [] ([], []) end;


(* syn_ext_consts *)

val binder_stamp = stamp ();
val binder_name = suffix "_binder";

fun syn_ext_consts is_logtype const_decls =
  let
    fun mk_infix sy ty c p1 p2 p3 =
      [Syn_Ext.Mfix ("op " ^ sy, ty, c, [], Syn_Ext.max_pri),
       Syn_Ext.Mfix ("(_ " ^ sy ^ "/ _)", ty, c, [p1, p2], p3)];

    fun binder_typ _ (Type ("fun", [Type ("fun", [_, ty2]), ty3])) =
          [Type ("idts", []), ty2] ---> ty3
      | binder_typ c _ = error ("Bad type of binder: " ^ quote c);

    fun mfix_of (_, _, NoSyn) = []
      | mfix_of (c, ty, Mixfix (sy, ps, p)) = [Syn_Ext.Mfix (sy, ty, c, ps, p)]
      | mfix_of (c, ty, Delimfix sy) = [Syn_Ext.Mfix (sy, ty, c, [], Syn_Ext.max_pri)]
      | mfix_of (c, ty, Infix (sy, p)) = mk_infix sy ty c (p + 1) (p + 1) p
      | mfix_of (c, ty, Infixl (sy, p)) = mk_infix sy ty c p (p + 1) p
      | mfix_of (c, ty, Infixr (sy, p)) = mk_infix sy ty c (p + 1) p p
      | mfix_of (c, ty, Binder (sy, p, q)) =
          [Syn_Ext.Mfix ("(3" ^ sy ^ "_./ _)", binder_typ c ty, (binder_name c), [0, p], q)]
      | mfix_of (c, _, _) = error ("Bad mixfix declaration for " ^ quote c);   (* FIXME printable c (!?) *)

    fun binder (c, _, Binder _) = SOME (binder_name c, c)
      | binder _ = NONE;

    val mfix = maps mfix_of const_decls;
    val xconsts = map #1 const_decls;
    val binders = map_filter binder const_decls;
    val binder_trs = binders
      |> map (Syn_Ext.stamp_trfun binder_stamp o apsnd K o Syn_Trans.mk_binder_tr);
    val binder_trs' = binders
      |> map (Syn_Ext.stamp_trfun binder_stamp o
          apsnd (K o Syn_Trans.non_typed_tr') o Syn_Trans.mk_binder_tr' o swap);
  in
    Syn_Ext.syn_ext' true is_logtype
      mfix xconsts ([], binder_trs, binder_trs', []) [] ([], [])
  end;

end;
