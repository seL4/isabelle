structure Prolog =
struct

local
 val parse_ast_translation = []
 val parse_preproc = None
 val parse_postproc = None
 val parse_translation = []
 val print_translation = []
 val print_preproc = None
 val print_postproc = None
 val print_ast_translation = []
in

(**** begin of user section ****)

(**** end of user section ****)

val thy = extend_theory (FOL.thy)
 "Prolog"
 ([],
  [],
  [(["list"], 1)],
  [(["list"], ([["term"]], "term"))],
  [(["Nil"], "'a list"),
   (["app"], "['a list, 'a list, 'a list] => o"),
   (["rev"], "['a list, 'a list] => o")],
  Some (NewSext {
   mixfix =
    [Infixr(":", "['a, 'a list]=> 'a list", 60)],
   xrules =
    [],
   parse_ast_translation = parse_ast_translation,
   parse_preproc = parse_preproc,
   parse_postproc = parse_postproc,
   parse_translation = parse_translation,
   print_translation = print_translation,
   print_preproc = print_preproc,
   print_postproc = print_postproc,
   print_ast_translation = print_ast_translation}))
 [("appNil", "app(Nil,ys,ys)"),
  ("appCons", "app(xs,ys,zs) ==> app(x:xs, ys, x:zs)"),
  ("revNil", "rev(Nil,Nil)"),
  ("revCons", "[| rev(xs,ys);  app(ys, x:Nil, zs) |] ==> rev(x:xs, zs)")]

val ax = get_axiom thy

val appNil = ax "appNil"
val appCons = ax "appCons"
val revNil = ax "revNil"
val revCons = ax "revCons"


end
end
