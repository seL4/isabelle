structure List =
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

val thy = extend_theory (Nat2.thy)
 "List"
 ([],
  [],
  [(["list"], 1)],
  [(["list"], ([["term"]], "term"))],
  [(["hd"], "'a list => 'a"),
   (["tl"], "'a list => 'a list"),
   (["forall"], "['a list, 'a => o] => o"),
   (["len"], "'a list => nat"),
   (["at"], "['a list, nat] => 'a")],
  Some (NewSext {
   mixfix =
    [Delimfix("[]", "'a list", "[]"),
     Infixr(".", "['a, 'a list] => 'a list", 80),
     Infixr("++", "['a list, 'a list] => 'a list", 70)],
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
 [("list_ind", "[| P([]);  ALL x l. P(l)-->P(x.l) |] ==> All(P)"),
  ("forall_cong", "[| l = l';  !!x. P(x)<->P'(x) |] ==> forall(l,P) <-> forall(l',P')"),
  ("list_distinct1", "~[] = x.l"),
  ("list_distinct2", "~x.l = []"),
  ("list_free", "x.l = x'.l' <-> x=x' & l=l'"),
  ("app_nil", "[]++l = l"),
  ("app_cons", "(x.l)++l' = x.(l++l')"),
  ("tl_eq", "tl(m.q) = q"),
  ("hd_eq", "hd(m.q) = m"),
  ("forall_nil", "forall([],P)"),
  ("forall_cons", "forall(x.l,P) <-> P(x) & forall(l,P)"),
  ("len_nil", "len([]) = 0"),
  ("len_cons", "len(m.q) = succ(len(q))"),
  ("at_0", "at(m.q,0) = m"),
  ("at_succ", "at(m.q,succ(n)) = at(q,n)")]

val ax = get_axiom thy

val list_ind = ax "list_ind"
val forall_cong = ax "forall_cong"
val list_distinct1 = ax "list_distinct1"
val list_distinct2 = ax "list_distinct2"
val list_free = ax "list_free"
val app_nil = ax "app_nil"
val app_cons = ax "app_cons"
val tl_eq = ax "tl_eq"
val hd_eq = ax "hd_eq"
val forall_nil = ax "forall_nil"
val forall_cons = ax "forall_cons"
val len_nil = ax "len_nil"
val len_cons = ax "len_cons"
val at_0 = ax "at_0"
val at_succ = ax "at_succ"


end
end
