(*  Title:      Pure/Syntax/symbol_font.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

The Isabelle symbol font.
*)

signature SYMBOL_FONT =
sig
  val char_names: string list
  val char: string -> string
end;

structure SymbolFont : SYMBOL_FONT =
struct

(** the encoding vector **)

val enc_start = 160;
val enc_end = 255;

val enc_vector =
[
  "altspace", "Gamma", "Delta", "Theta", "Lambda", "Pi", "Sigma", "Phi",
  "Psi", "Omega", "alpha", "beta", "gamma", "delta", "epsilon", "zeta",
  "eta", "theta", "kappa", "lambda", "mu", "nu", "xi", "pi",
  "rho", "sigma", "tau", "phi", "chi", "psi", "omega", "neg",
  "vee", "wedge", "forall", "exists", "Vee", "lceil", "rceil", "lfloor",
  "rfloor", "ldpar", "rdpar", "ldbrak", "rdbrak", "empty", "in", "subseteq",
  "cap", "cup", "Cap", "Cup", "sqcap", "sqcup", "Sqcap", "Sqcup",
  "bottom", "doteq", "equiv", "noteq", "sqsubset", "sqsubseteq", "prec", "preceq",
  "succ", "succeq", "sim", "simeq", "le", "ge", "leftarrow", "midarrow",
  "rightarrow", "Leftarrow", "Midarrow", "Rightarrow", "rrightarrow", "mapsto", "leadsto", "up",
  "down", "notin", "times", "oplus", "ominus", "otimes", "oslash", "natural",
  "infty", "box", "diamond", "circ", "bullet", "parallel", "tick", "copyright"
];

val enc_tab = Symtab.make (enc_vector ~~ (enc_start upto enc_end));


(** chars by name **)

val char_names = enc_vector;

fun char name =
 (case Symtab.lookup (enc_tab, name) of
   None => error ("Unknown symbol name: " ^ quote name)
 | Some n => chr n);


end;
