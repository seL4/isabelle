(*  Title:      Pure/Syntax/token_trans.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Token translations for xterm and LaTeX output.
*)

signature TOKEN_TRANS =
sig
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

fun style s x = (s ^ x ^ normal, size x);


val xterm_trans =
 trans_mode "xterm"
  [("bound", style underline),
   ("free", style bold),
   ("var", style bold),
   ("tfree", style bold),
   ("tvar", style bold)];

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
