(*  Title:      HOL/Import/HOL/ROOT.ML
    ID:         $Id$
    Author:     Sebastian Skalberg (TU Muenchen)
*)

(* FIXME tmp hack to get generated theories work *)

local

fun old_add_constdefs args thy =
  thy
  |> Theory.add_consts (map fst args)
  |> IsarThy.add_defs (false, map (fn ((c, _, mx), s) =>
    ((Thm.def_name (Syntax.const_name c mx), s), [])) args);

structure P = OuterParse and K = OuterSyntax.Keyword;

val constdefsP =
  OuterSyntax.command "constdefs" "declare and define constants (old style)"
    K.thy_decl
    (Scan.repeat1 (P.const -- P.term) >> (Toplevel.theory o old_add_constdefs));

in

val _ = OuterSyntax.add_parsers [constdefsP];

end;

with_path ".." use_thy "HOL4Compat";
with_path ".." use_thy "HOL4Syntax";
setmp quick_and_dirty true use_thy "HOL4Prob";
setmp quick_and_dirty true use_thy "HOL4";
