(*  Title:      Pure/Syntax/token_trans.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Token translations for xterm output.
*)

signature TOKEN_TRANS0 =
sig
  val standard_token_classes: string list
  val tokentrans_mode: string -> (string * (string -> string * real)) list ->
    (string * string * (string -> string * real)) list
end;

signature TOKEN_TRANS =
sig
  include TOKEN_TRANS0
  val standard_token_markers: string list
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
  val token_translation: (string * string * (string -> string * real)) list
end;

structure TokenTrans: TOKEN_TRANS =
struct


(** misc utils **)

fun tokentrans_mode m trs = map (fn (s, f) => (m, s, f)) trs;

val standard_token_classes =
  ["class", "tfree", "tvar", "free", "bound", "var", "num", "xnum", "xstr"];

val standard_token_markers = map (fn s => "_" ^ s) standard_token_classes;


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

fun style (ref s) x = Output.output_width x |> apfst (enclose s normal);


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
 tokentrans_mode "xterm"
  [("class", style xterm_class),
   ("tfree", style xterm_tfree),
   ("tvar", style xterm_tvar),
   ("free", style xterm_free),
   ("bound", style xterm_bound),
   ("var", style xterm_var)] @
 tokentrans_mode "xterm_color"
  [("class", style xterm_color_class),
   ("tfree", style xterm_color_tfree),
   ("tvar", style xterm_color_tvar),
   ("free", style xterm_color_free),
   ("bound", style xterm_color_bound),
   ("var", style xterm_color_var)];



(** standard token translations **)

val token_translation =
  map (fn s => ("", s, Output.output_width)) standard_token_classes @
  xterm_trans;


end;
