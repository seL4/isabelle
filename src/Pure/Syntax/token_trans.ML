(*  Title:      Pure/Syntax/token_trans.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Token translations for xterm and LaTeX output.
*)

signature TOKEN_TRANS =
sig
  val token_translation: (string * string * (string -> string * int)) list
  val class_style: string ref
  val tfree_style: string ref
  val tvar_style: string ref
  val free_style: string ref
  val bound_style: string ref
  val var_style: string ref
  val normal: string
  val bold: string
  val underline: string
  val reverse: string
  val black: string
  val red: string
  val green: string
  val yellow: string
  val blue: string
  val purple: string
  val cyan: string
  val white: string
end;

structure TokenTrans: TOKEN_TRANS =
struct

(** misc utils **)

fun trans_mode m trs = map (fn (s, f) => (m, s, f)) trs;

val tok_classes = ["class", "tfree", "tvar", "free", "bound", "var"];



(** xterm output **)

(* styles *)

val normal = "\^[[0m";
val bold = "\^[[1m";
val underline = "\^[[4m";
val reverse = "\^[[7m";

val black = "\^[[30m";		(**)
val red = "\^[[31m";		(**)
val green = "\^[[32m";		(**)
val yellow = "\^[[33m";
val blue = "\^[[34m";		(**)
val purple = "\^[[35m";		(**)
val cyan = "\^[[36m";
val white = "\^[[37m";

fun style s x = (s ^ x ^ normal, size x);
fun ref_style (ref s) x = (s ^ x ^ normal, size x);

val class_style = ref normal;
val tfree_style = ref bold;
val tvar_style = ref bold;
val free_style = ref bold;
val bound_style = ref underline;
val var_style = ref bold;


val xterm_trans =
 trans_mode "xterm"
  [("class", ref_style class_style),
   ("tfree", ref_style tfree_style),
   ("tvar", ref_style tvar_style),
   ("free", ref_style free_style),
   ("bound", ref_style bound_style),
   ("var", ref_style var_style)]


(* FIXME xterm-color *)


(** LaTeX output **)

(* FIXME 'a -> \alpha etc. *)


(** token translations **)

val token_translation =
  map (fn s => ("", s, fn x => (x, size x))) tok_classes @
  (* FIXME tmp test *)
  map (fn s => ("test", s, fn x => (s ^ "[" ^ x ^ "]", size x + size s + 2))) tok_classes @
  xterm_trans;


end;
