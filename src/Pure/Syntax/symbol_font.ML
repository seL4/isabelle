(*  Title:      Pure/Syntax/symbol_font.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

The Isabelle symbol font.
*)

signature SYMBOL_FONT =
sig
  val char_names: string list
  val char: string -> string option
end;

structure SymbolFont : SYMBOL_FONT =
struct

(** the encoding vector **)

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

val enc_tab = Symtab.make (enc_vector ~~ (enc_start upto enc_end));


(** chars by name **)

val char_names = enc_vector;

fun char name = apsome chr (Symtab.lookup (enc_tab, name));

end;
