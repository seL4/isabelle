(*  Title:      Pure/Isar/term_style.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Styles for terms, to use with the "term_style" and "thm_style" antiquotations
*)

signature STYLE =
sig
  val get_style: theory -> string -> (Term.term -> Term.term)
  val put_style: string -> (Term.term -> Term.term) -> theory -> theory
end;

structure Style: STYLE =
struct

(* exception *)
exception STYLE of string;

(* style data *)
structure StyleArgs =
struct
  val name = "Isar/style";
  type T = (string * (Term.term -> Term.term)) list;
  val empty = [];
  val copy = I;
  val prep_ext = I;
  fun merge (a1, a2) = Library.foldl Library.overwrite (a1, a2);
    (* piecewise update of a1 by a2 *)
  fun print _ _ = raise (STYLE "cannot print style (not implemented)");
end;

structure StyleData = TheoryDataFun(StyleArgs);

(* accessors *)
fun get_style thy name =
  case Library.assoc_string ((StyleData.get thy), name)
    of NONE => raise (STYLE ("no style named " ^ name))
     | SOME style => style

fun put_style name style thy =
  StyleData.put (Library.overwrite ((StyleData.get thy), (name, style))) thy;

(* predefined styles *)
fun style_lhs (Const ("==", _) $ t $ _) = t
  | style_lhs (Const ("Trueprop", _) $ t) = style_lhs t
  | style_lhs (Const ("==>", _) $ _ $ t) = style_lhs t
  | style_lhs (_ $ t $ _) = t
  | style_lhs _ = error ("Binary operator expected")

fun style_rhs (Const ("==", _) $ _ $ t) = t
  | style_rhs (Const ("Trueprop", _) $ t) = style_rhs t
  | style_rhs (Const ("==>", _) $ _ $ t) = style_rhs t
  | style_rhs (_ $ _ $ t) = t
  | style_rhs _ = error ("Binary operator expected")

(* initialization *)
val _ = Context.add_setup [StyleData.init,
  put_style "lhs" style_lhs,
  put_style "rhs" style_rhs,
  put_style "conclusion" Logic.strip_imp_concl
];

end;
