(*  Title:      Pure/Syntax/symbol_font.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

The Isabelle symbol font.
*)

signature SYMBOL_FONT =
sig
  val char: string -> string option
  val name: string -> string option
  val read_charnames: string list -> string list
  val read_chnames: string -> string
  val write_charnames: string list -> string list	(*normal backslashes*)
  val write_chnames: string -> string
  val write_charnames': string list -> string list	(*escaped backslashes*)
  val write_chnames': string -> string
end;


structure SymbolFont : SYMBOL_FONT =
struct


(** font encoding vector **)

(* tables *)

val enc_start = 161;
val enc_end = 255;

val enc_vector =
[
(* GENERATED TEXT FOLLOWS - Do not edit! *)
  "space2",
  "Gamma",
  "Delta",
  "Theta",
  "Lambda",
  "Pi",
  "Sigma",
  "Phi",
  "Psi",
  "Omega",
  "alpha",
  "beta",
  "gamma",
  "delta",
  "epsilon",
  "zeta",
  "eta",
  "theta",
  "kappa",
  "lambda",
  "mu",
  "nu",
  "xi",
  "pi",
  "rho",
  "sigma",
  "tau",
  "phi",
  "chi",
  "psi",
  "omega",
  "not",
  "and",
  "or",
  "forall",
  "exists",
  "And",
  "lceil",
  "rceil",
  "lfloor",
  "rfloor",
  "turnstile",
  "Turnstile",
  "lbrakk",
  "rbrakk",
  "cdot",
  "in",
  "subseteq",
  "inter",
  "union",
  "Inter",
  "Union",
  "sqinter",
  "squnion",
  "Sqinter",
  "Squnion",
  "bottom",
  "doteq",
  "equiv",
  "noteq",
  "sqsubset",
  "sqsubseteq",
  "prec",
  "preceq",
  "succ",
  "approx",
  "sim",
  "simeq",
  "le",
  "Colon",
  "leftarrow",
  "midarrow",
  "rightarrow",
  "Leftarrow",
  "Midarrow",
  "Rightarrow",
  "bow",
  "mapsto",
  "leadsto",
  "up",
  "down",
  "notin",
  "times",
  "oplus",
  "ominus",
  "otimes",
  "oslash",
  "subset",
  "infinity",
  "box",
  "diamond",
  "circ",
  "bullet",
  "parallel",
  "surd",
  "copyright"
(* END OF GENERATED TEXT *)
];

val enc_rel = enc_vector ~~ (map chr (enc_start upto enc_end));

val enc_tab = Symtab.make enc_rel;
val dec_tab = Symtab.make (map swap enc_rel);


(* chars and names *)

fun char name = Symtab.lookup (enc_tab, name);

fun name char =
  if ord char < enc_start then None
  else Symtab.lookup (dec_tab, char);



(** input and output of symbols **)

(* read_charnames *)

local
  open Scanner;

  fun scan_symbol ("\\" :: "<" :: cs) =
        let
          val (name, cs') = (scan_id -- $$ ">" >> #1) cs handle LEXICAL_ERROR
            => error ("Malformed symbolic char specification: \"\\<" ^ implode cs ^ "\"");
          val c = the (char name) handle OPTION _
            => error ("Unknown symbolic char name: " ^ quote name);
        in (c, cs') end
    | scan_symbol _ = raise LEXICAL_ERROR;
in
  fun read_charnames chs =
    if forall (not_equal "\\") chs then chs
    else #1 (repeat (scan_symbol || scan_one (K true)) chs);

  val read_chnames = implode o read_charnames o explode;
end;


(* write_charnames *)

fun write_char prfx ch =
  (case name ch of
    None => ch
  | Some nm => prfx ^ "\\<" ^ nm ^ ">");

fun write_chars prfx chs =
  if forall (fn ch => ord ch < enc_start) chs then chs
  else map (write_char prfx) chs;

val write_charnames = write_chars "";
val write_charnames' = write_chars "\\";

val write_chnames = implode o write_charnames o explode;
val write_chnames' = implode o write_charnames' o explode;

end;
