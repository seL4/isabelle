(*  Title:      Pure/Syntax/mixfix.ML
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

Mixfix declarations, infixes, binders.
*)

signature BASIC_MIXFIX =
sig
  datatype mixfix =
    NoSyn |
    Mixfix of Input.source * int list * int * Position.range |
    Delimfix of Input.source * Position.range |
    Infix of Input.source * int * Position.range |
    Infixl of Input.source * int * Position.range |
    Infixr of Input.source * int * Position.range |
    Binder of Input.source * int * int * Position.range |
    Structure of Position.range
end;

signature MIXFIX =
sig
  include BASIC_MIXFIX
  val is_empty: mixfix -> bool
  val equal: mixfix * mixfix -> bool
  val set_range: Position.range -> mixfix -> mixfix
  val range_of: mixfix -> Position.range
  val pos_of: mixfix -> Position.T
  val reset_pos: mixfix -> mixfix
  val pretty_mixfix: mixfix -> Pretty.T
  val mixfix_args: mixfix -> int
  val mixfixT: mixfix -> typ
  val make_type: int -> typ
  val binder_name: string -> string
  val syn_ext_types: (string * typ * mixfix) list -> Syntax_Ext.syn_ext
  val syn_ext_consts: string list -> (string * typ * mixfix) list -> Syntax_Ext.syn_ext
end;

structure Mixfix: MIXFIX =
struct

(** mixfix declarations **)

datatype mixfix =
  NoSyn |
  Mixfix of Input.source * int list * int * Position.range |
  Delimfix of Input.source * Position.range |
  Infix of Input.source * int * Position.range |
  Infixl of Input.source * int * Position.range |
  Infixr of Input.source * int * Position.range |
  Binder of Input.source * int * int * Position.range |
  Structure of Position.range;

fun is_empty NoSyn = true
  | is_empty _ = false;

fun equal (NoSyn, NoSyn) = true
  | equal (Mixfix (sy, ps, p, _), Mixfix (sy', ps', p', _)) =
      Input.equal_content (sy, sy') andalso ps = ps' andalso p = p'
  | equal (Delimfix (sy, _), Delimfix (sy', _)) = Input.equal_content (sy, sy')
  | equal (Infix (sy, p, _), Infix (sy', p', _)) = Input.equal_content (sy, sy') andalso p = p'
  | equal (Infixl (sy, p, _), Infixl (sy', p', _)) = Input.equal_content (sy, sy') andalso p = p'
  | equal (Infixr (sy, p, _), Infixr (sy', p', _)) = Input.equal_content (sy, sy') andalso p = p'
  | equal (Binder (sy, p, q, _), Binder (sy', p', q', _)) =
      Input.equal_content (sy, sy') andalso p = p' andalso q = q'
  | equal (Structure _, Structure _) = true
  | equal _ = false;

fun set_range range mx =
  (case mx of
    NoSyn => NoSyn
  | Mixfix (sy, ps, p, _) => Mixfix (sy, ps, p, range)
  | Delimfix (sy, _) => Delimfix (sy, range)
  | Infix (sy, p, _) => Infix (sy, p, range)
  | Infixl (sy, p, _) => Infixl (sy, p, range)
  | Infixr (sy, p, _) => Infixr (sy, p, range)
  | Binder (sy, p, q, _) => Binder (sy, p, q, range)
  | Structure _ => Structure range);

fun range_of NoSyn = Position.no_range
  | range_of (Mixfix (_, _, _, range)) = range
  | range_of (Delimfix (_, range)) = range
  | range_of (Infix (_, _, range)) = range
  | range_of (Infixl (_, _, range)) = range
  | range_of (Infixr (_, _, range)) = range
  | range_of (Binder (_, _, _, range)) = range
  | range_of (Structure range) = range;

val pos_of = Position.set_range o range_of;

fun reset_pos NoSyn = NoSyn
  | reset_pos (Mixfix (sy, ps, p, _)) = Mixfix (Input.reset_pos sy, ps, p, Position.no_range)
  | reset_pos (Delimfix (sy, _)) = Delimfix (Input.reset_pos sy, Position.no_range)
  | reset_pos (Infix (sy, p, _)) = Infix (Input.reset_pos sy, p, Position.no_range)
  | reset_pos (Infixl (sy, p, _)) = Infixl (Input.reset_pos sy, p, Position.no_range)
  | reset_pos (Infixr (sy, p, _)) = Infixr (Input.reset_pos sy, p, Position.no_range)
  | reset_pos (Binder (sy, p, q, _)) = Binder (Input.reset_pos sy, p, q, Position.no_range)
  | reset_pos (Structure _) = Structure Position.no_range;


(* pretty_mixfix *)

local

val quoted = Pretty.quote o Pretty.str o Input.source_content;
val keyword = Pretty.keyword2;
val parens = Pretty.enclose "(" ")";
val brackets = Pretty.enclose "[" "]";
val int = Pretty.str o string_of_int;

in

fun pretty_mixfix NoSyn = Pretty.str ""
  | pretty_mixfix (Mixfix (s, ps, p, _)) =
      parens (Pretty.breaks [quoted s, brackets (Pretty.commas (map int ps)), int p])
  | pretty_mixfix (Delimfix (s, _)) = parens [quoted s]
  | pretty_mixfix (Infix (s, p, _)) = parens (Pretty.breaks [keyword "infix", quoted s, int p])
  | pretty_mixfix (Infixl (s, p, _)) = parens (Pretty.breaks [keyword "infixl", quoted s, int p])
  | pretty_mixfix (Infixr (s, p, _)) = parens (Pretty.breaks [keyword "infixl", quoted s, int p])
  | pretty_mixfix (Binder (s, p1, p2, _)) =
      parens (Pretty.breaks [keyword "binder", quoted s, brackets [int p1], int p2])
  | pretty_mixfix (Structure _) = parens [keyword "structure"];

end;


(* syntax specifications *)

fun mixfix_args NoSyn = 0
  | mixfix_args (Mixfix (sy, _, _, _)) = Syntax_Ext.mixfix_args sy
  | mixfix_args (Delimfix (sy, _)) = Syntax_Ext.mixfix_args sy
  | mixfix_args (Infix (sy, _, _)) = 2 + Syntax_Ext.mixfix_args sy
  | mixfix_args (Infixl (sy, _, _)) = 2 + Syntax_Ext.mixfix_args sy
  | mixfix_args (Infixr (sy, _, _)) = 2 + Syntax_Ext.mixfix_args sy
  | mixfix_args (Binder _) = 1
  | mixfix_args (Structure _) = 0;

fun mixfixT (Binder _) = (dummyT --> dummyT) --> dummyT
  | mixfixT mx = replicate (mixfix_args mx) dummyT ---> dummyT;


(* syn_ext_types *)

val typeT = Type ("type", []);
fun make_type n = replicate n typeT ---> typeT;

fun syn_ext_types type_decls =
  let
    fun mk_infix sy ty t p1 p2 p3 range =
      Syntax_Ext.Mfix
        (Symbol_Pos.explode0 "(_ " @ Input.source_explode sy @ Symbol_Pos.explode0 "/ _)",
          ty, t, [p1, p2], p3, Position.set_range range);

    fun mfix_of (_, _, NoSyn) = NONE
      | mfix_of (t, ty, Mixfix (sy, ps, p, range)) =
          SOME (Syntax_Ext.Mfix (Input.source_explode sy, ty, t, ps, p, Position.set_range range))
      | mfix_of (t, ty, Delimfix (sy, range)) =
          SOME (Syntax_Ext.Mfix (Input.source_explode sy, ty, t, [], 1000, Position.set_range range))
      | mfix_of (t, ty, Infix (sy, p, range)) = SOME (mk_infix sy ty t (p + 1) (p + 1) p range)
      | mfix_of (t, ty, Infixl (sy, p, range)) = SOME (mk_infix sy ty t p (p + 1) p range)
      | mfix_of (t, ty, Infixr (sy, p, range)) = SOME (mk_infix sy ty t (p + 1) p p range)
      | mfix_of (t, _, _) = error ("Bad mixfix declaration for " ^ quote t);

    fun check_args (_, ty, mx) (SOME (Syntax_Ext.Mfix (sy, _, _, _, _, _))) =
          if length (Term.binder_types ty) = Syntax_Ext.mfix_args sy then ()
          else
            error ("Bad number of type constructor arguments in mixfix annotation" ^
              Position.here (pos_of mx))
      | check_args _ NONE = ();

    val mfix = map mfix_of type_decls;
    val _ = map2 check_args type_decls mfix;
    val consts = map (fn (t, _, _) => (t, "")) type_decls;
  in Syntax_Ext.syn_ext (map_filter I mfix) consts ([], [], [], []) ([], []) end;


(* syn_ext_consts *)

val binder_stamp = stamp ();
val binder_name = suffix "_binder";

fun syn_ext_consts logical_types const_decls =
  let
    fun mk_infix sy ty c p1 p2 p3 range =
      [Syntax_Ext.Mfix
        (Symbol_Pos.explode0 "op " @ Input.source_explode sy,
          ty, c, [], 1000, Position.set_range range),
       Syntax_Ext.Mfix
        (Symbol_Pos.explode0 "(_ " @ Input.source_explode sy @ Symbol_Pos.explode0 "/ _)",
          ty, c, [p1, p2], p3, Position.set_range range)];

    fun binder_typ _ (Type ("fun", [Type ("fun", [_, ty2]), ty3])) =
          [Type ("idts", []), ty2] ---> ty3
      | binder_typ c _ = error ("Bad type of binder: " ^ quote c);

    fun mfix_of (_, _, NoSyn) = []
      | mfix_of (c, ty, Mixfix (sy, ps, p, range)) =
          [Syntax_Ext.Mfix (Input.source_explode sy, ty, c, ps, p, Position.set_range range)]
      | mfix_of (c, ty, Delimfix (sy, range)) =
          [Syntax_Ext.Mfix (Input.source_explode sy, ty, c, [], 1000, Position.set_range range)]
      | mfix_of (c, ty, Infix (sy, p, range)) = mk_infix sy ty c (p + 1) (p + 1) p range
      | mfix_of (c, ty, Infixl (sy, p, range)) = mk_infix sy ty c p (p + 1) p range
      | mfix_of (c, ty, Infixr (sy, p, range)) = mk_infix sy ty c (p + 1) p p range
      | mfix_of (c, ty, Binder (sy, p, q, range)) =
          [Syntax_Ext.Mfix
            (Symbol_Pos.explode0 "(3" @ Input.source_explode sy @ Symbol_Pos.explode0 "_./ _)",
              binder_typ c ty, (binder_name c), [0, p], q, Position.set_range range)]
      | mfix_of (c, _, mx) =
          error ("Bad mixfix declaration for " ^ quote c ^ Position.here (pos_of mx));

    fun binder (c, _, Binder _) = SOME (binder_name c, c)
      | binder _ = NONE;

    val mfix = maps mfix_of const_decls;
    val binders = map_filter binder const_decls;
    val binder_trs = binders
      |> map (Syntax_Ext.stamp_trfun binder_stamp o Syntax_Trans.mk_binder_tr);
    val binder_trs' = binders
      |> map (Syntax_Ext.stamp_trfun binder_stamp o
          apsnd Syntax_Trans.non_typed_tr' o Syntax_Trans.mk_binder_tr' o swap);

    val consts = binders @ map (fn (c, _, _) => (c, "")) const_decls;
  in
    Syntax_Ext.syn_ext' logical_types mfix consts ([], binder_trs, binder_trs', []) ([], [])
  end;

end;

structure Basic_Mixfix: BASIC_MIXFIX = Mixfix;
open Basic_Mixfix;
