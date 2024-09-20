(*  Title:      HOL/ex/Multiquote.thy
    Author:     Markus Wenzel, TU Muenchen
*)

section \<open>Multiple nested quotations and anti-quotations\<close>

theory Multiquote
imports Main
begin

text \<open>
  Multiple nested quotations and anti-quotations -- basically a
  generalized version of de-Bruijn representation.
\<close>

syntax
  "_quote" :: "'b \<Rightarrow> ('a \<Rightarrow> 'b)"    (\<open>\<guillemotleft>_\<guillemotright>\<close> [0] 1000)
  "_antiquote" :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b"    (\<open>\<acute>_\<close> [1000] 1000)

parse_translation \<open>
  let
    fun antiquote_tr i (Const (\<^syntax_const>\<open>_antiquote\<close>, _) $
          (t as Const (\<^syntax_const>\<open>_antiquote\<close>, _) $ _)) = skip_antiquote_tr i t
      | antiquote_tr i (Const (\<^syntax_const>\<open>_antiquote\<close>, _) $ t) =
          antiquote_tr i t $ Bound i
      | antiquote_tr i (t $ u) = antiquote_tr i t $ antiquote_tr i u
      | antiquote_tr i (Abs (x, T, t)) = Abs (x, T, antiquote_tr (i + 1) t)
      | antiquote_tr _ a = a
    and skip_antiquote_tr i ((c as Const (\<^syntax_const>\<open>_antiquote\<close>, _)) $ t) =
          c $ skip_antiquote_tr i t
      | skip_antiquote_tr i t = antiquote_tr i t;

    fun quote_tr [t] = Abs ("s", dummyT, antiquote_tr 0 (Term.incr_boundvars 1 t))
      | quote_tr ts = raise TERM ("quote_tr", ts);
  in [(\<^syntax_const>\<open>_quote\<close>, K quote_tr)] end
\<close>

text \<open>basic examples\<close>
term "\<guillemotleft>a + b + c\<guillemotright>"
term "\<guillemotleft>a + b + c + \<acute>x + \<acute>y + 1\<guillemotright>"
term "\<guillemotleft>\<acute>(f w) + \<acute>x\<guillemotright>"
term "\<guillemotleft>f \<acute>x \<acute>y z\<guillemotright>"

text \<open>advanced examples\<close>
term "\<guillemotleft>\<guillemotleft>\<acute>\<acute>x + \<acute>y\<guillemotright>\<guillemotright>"
term "\<guillemotleft>\<guillemotleft>\<acute>\<acute>x + \<acute>y\<guillemotright> \<circ> \<acute>f\<guillemotright>"
term "\<guillemotleft>\<acute>(f \<circ> \<acute>g)\<guillemotright>"
term "\<guillemotleft>\<guillemotleft>\<acute>\<acute>(f \<circ> \<acute>g)\<guillemotright>\<guillemotright>"

end
