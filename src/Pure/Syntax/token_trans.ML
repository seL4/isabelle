(*  Title:      Pure/Syntax/token_trans.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Token translations for xterm and LaTeX output.
*)

signature TOKEN_TRANS =
sig
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
  val xterm_class: string ref
  val xterm_tfree: string ref
  val xterm_tvar: string ref
  val xterm_free: string ref
  val xterm_bound: string ref
  val xterm_var: string ref
  val xterm_color_class: string ref
  val xterm_color_tfree: string ref
  val xterm_color_tvar: string ref
  val xterm_color_free: string ref
  val xterm_color_bound: string ref
  val xterm_color_var: string ref
  val token_translation: (string * string * (string -> string * int)) list
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

val black = "\^[[30m";
val red = "\^[[31m";
val green = "\^[[32m";
val yellow = "\^[[33m";
val blue = "\^[[34m";
val purple = "\^[[35m";
val cyan = "\^[[36m";
val white = "\^[[37m";

fun style (ref s) x = (s ^ x ^ normal, size x);


(* print modes "xterm" and "xterm_color" *)

val xterm_class = ref normal;
val xterm_tfree = ref bold;
val xterm_tvar = ref bold;
val xterm_free = ref bold;
val xterm_bound = ref underline;
val xterm_var = ref bold;

val xterm_color_class = ref red;
val xterm_color_tfree = ref purple;
val xterm_color_tvar = ref purple;
val xterm_color_free = ref blue;
val xterm_color_bound = ref green;
val xterm_color_var = ref blue;

val xterm_trans =
 trans_mode "xterm"
  [("class", style xterm_class),
   ("tfree", style xterm_tfree),
   ("tvar", style xterm_tvar),
   ("free", style xterm_free),
   ("bound", style xterm_bound),
   ("var", style xterm_var)] @
 trans_mode "xterm_color"
  [("class", style xterm_color_class),
   ("tfree", style xterm_color_tfree),
   ("tvar", style xterm_color_tvar),
   ("free", style xterm_color_free),
   ("bound", style xterm_color_bound),
   ("var", style xterm_color_var)];


(** LaTeX output **)

(* FIXME 'a -> \alpha etc. *)


(** token translations **)

val token_translation =
  map (fn s => ("", s, fn x => (x, size x))) tok_classes @
  (* FIXME tmp test *)
  map (fn s => ("test", s, fn x => (s ^ "[" ^ x ^ "]", size x + size s + 2))) tok_classes @
  xterm_trans;


end;
