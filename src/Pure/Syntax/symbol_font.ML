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
  val write_charnames:  string list -> string list
end;


structure SymbolFont : SYMBOL_FONT =
struct


(** font encoding vector **)

(* tables *)

val enc_start = 161;
val enc_end = 255;

val enc_vector =
[
      "Gamma", "Delta", "Theta", "Lambda", "Pi", "Sigma", "Phi",
  "Psi", "Omega", "alpha", "beta", "gamma", "delta", "epsilon", "zeta",
  "eta", "theta", "kappa", "lambda", "mu", "nu", "xi", "pi",
  "rho", "sigma", "tau", "phi", "chi", "psi", "omega", "not",
  "and", "or", "forall", "exists", "And", "lceil", "rceil", "lfloor",
  "rfloor", "lparr", "rparr", "lbrakk", "rbrakk", "empty", "in", "subseteq",
  "inter", "union", "Inter", "Union", "sqinter", "squnion", "Sqinter", "Squnion",
  "bottom", "doteq", "equiv", "noteq", "sqsubset", "sqsubseteq", "prec", "preceq",
  "succ", "succeq", "sim", "simeq", "le", "ge", "leftarrow", "midarrow",
  "rightarrow", "Leftarrow", "Midarrow", "Rightarrow", "rrightarrow", "mapsto", "leadsto", "up",
  "down", "notin", "times", "oplus", "ominus", "otimes", "oslash", "natural",
  "infinity", "box", "diamond", "circ", "bullet", "parallel", "tick", "copyright"
];

val enc_rel = enc_vector ~~ (map chr (enc_start upto enc_end));

val enc_tab = Symtab.make enc_rel;
val dec_tab = Symtab.make (map swap enc_rel);


(* chars and names *)

fun char name = Symtab.lookup (enc_tab, name);
fun name char = Symtab.lookup (dec_tab, char);



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
  val read_charnames = #1 o repeat (scan_symbol || scan_one (K true));
end;


(* write_charnames *)

fun write_char ch =
  (case name ch of
    None => ch
  | Some nm => "\\<" ^ nm ^ ">");

val write_charnames = map write_char;


end;
