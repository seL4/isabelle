(*  Title:      Pure/Syntax/token_trans.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Token translations for xterm, emacs and latex output.

TODO:
  - elim this file, move stuff to individual print/presentation modes (!?);
*)

signature TOKEN_TRANS0 =
sig
  val standard_token_classes: string list
end;

signature TOKEN_TRANS =
sig
  include TOKEN_TRANS0
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

fun trans_mode m trs = map (fn (s, f) => (m, s, f)) trs;

val standard_token_classes =
  ["class", "tfree", "tvar", "free", "bound", "var", "xnum", "xstr"];



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

fun style (ref s) x = (s ^ x ^ normal, real (size x));


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



(** emacs output (Isamode) **)

local

val end_tag = "\^A0";
val tclass_tag = "\^A1";
val tfree_tag = "\^A2";
val tvar_tag = "\^A3";
val free_tag = "\^A4";
val bound_tag = "\^A5";
val var_tag = "\^A6";

fun tagit p x = (p ^ x ^ end_tag, real (size x));

in

val emacs_trans =
 trans_mode "emacs"
  [("class", tagit tclass_tag),
   ("tfree", tagit tfree_tag),
   ("tvar", tagit tvar_tag),
   ("free", tagit free_tag),
   ("bound", tagit bound_tag),
   ("var", tagit var_tag)];

end;



(** ProofGeneral output **)

local

val end_tag = oct_char "350";
val tclass_tag = oct_char "351";
val tfree_tag = oct_char "352";
val tvar_tag = oct_char "353";
val free_tag = oct_char "354";
val bound_tag = oct_char "355";
val var_tag = oct_char "356";

fun tagit p x = (p ^ x ^ end_tag, real (size x));

in

val proof_general_trans =
 trans_mode "ProofGeneral"
  [("class", tagit tclass_tag),
   ("tfree", tagit tfree_tag),
   ("tvar", tagit tvar_tag),
   ("free", tagit free_tag),
   ("bound", tagit bound_tag),
   ("var", tagit var_tag)];

end;



(** LaTeX output **)

(* FIXME 'a -> \alpha etc. *)

val latex_trans =
 trans_mode "latex" [] : (string * string * (string -> string * real)) list;



(** standard token translations **)

val token_translation =
  map (fn s => ("", s, fn x => (x, real (size x)))) standard_token_classes @
  xterm_trans @
  emacs_trans @
  proof_general_trans @
  latex_trans;


end;
