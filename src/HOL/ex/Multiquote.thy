(*  Title:      HOL/ex/Multiquote.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

header {* Multiple nested quotations and anti-quotations *}

theory Multiquote = Main:

text {*
  Multiple nested quotations and anti-quotations -- basically a
  generalized version of de-Bruijn representation.
*}

syntax
  "_quote" :: "'b => ('a => 'b)"	     (".'(_')." [0] 1000)
  "_antiquote" :: "('a => 'b) => 'b"         ("\<acute>_" [1000] 1000)

parse_translation {*
  let
    fun antiquote_tr i (Const ("_antiquote", _) $ (t as Const ("_antiquote", _) $ _)) =
          skip_antiquote_tr i t
      | antiquote_tr i (Const ("_antiquote", _) $ t) =
          antiquote_tr i t $ Bound i
      | antiquote_tr i (t $ u) = antiquote_tr i t $ antiquote_tr i u
      | antiquote_tr i (Abs (x, T, t)) = Abs (x, T, antiquote_tr (i + 1) t)
      | antiquote_tr _ a = a
    and skip_antiquote_tr i ((c as Const ("_antiquote", _)) $ t) =
          c $ skip_antiquote_tr i t
      | skip_antiquote_tr i t = antiquote_tr i t;

    fun quote_tr [t] = Abs ("s", dummyT, antiquote_tr 0 (Term.incr_boundvars 1 t))
      | quote_tr ts = raise TERM ("quote_tr", ts);
  in [("_quote", quote_tr)] end
*}

text {* basic examples *}
term ".(a + b + c)."
term ".(a + b + c + \<acute>x + \<acute>y + 1)."
term ".(\<acute>(f w) + \<acute>x)."
term ".(f \<acute>x \<acute>y z)."

text {* advanced examples *}
term ".(.(\<acute>\<acute>x + \<acute>y).)."
term ".(.(\<acute>\<acute>x + \<acute>y). \<circ> \<acute>f)."
term ".(\<acute>(f \<circ> \<acute>g))."
term ".(.( \<acute>\<acute>(f \<circ> \<acute>g) ).)."

end
