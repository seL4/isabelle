(*  Title:      HOL/ex/Term_Of_Syntax.thy
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Input syntax for term_of functions *}

theory Term_Of_Syntax
imports Code_Eval
begin

setup {*
  Sign.declare_const [] ((Binding.name "rterm_of", @{typ "'a \<Rightarrow> 'b"}), NoSyn)
  #> snd
*}

notation (output)
  rterm_of ("\<guillemotleft>_\<guillemotright>")

locale rterm_syntax =
  fixes rterm_of_syntax :: "'a \<Rightarrow> 'b" ("\<guillemotleft>_\<guillemotright>")

parse_translation {*
let
  fun rterm_of_tr [t] = Lexicon.const @{const_name rterm_of} $ t
    | rterm_of_tr ts = raise TERM ("rterm_of_tr", ts);
in
  [(Syntax.fixedN ^ "rterm_of_syntax", rterm_of_tr)]
end
*}

setup {*
let
  val subst_rterm_of = map_aterms
    (fn Free (v, _) => error ("illegal free variable in term quotation: " ^ quote v) | t => t)
      o HOLogic.reflect_term;
  fun subst_rterm_of' (Const (@{const_name rterm_of}, _), [t]) = subst_rterm_of t
    | subst_rterm_of' (Const (@{const_name rterm_of}, _), _) =
        error ("illegal number of arguments for " ^ quote @{const_name rterm_of})
    | subst_rterm_of' (t, ts) = list_comb (t, map (subst_rterm_of' o strip_comb) ts);
  fun subst_rterm_of'' t = 
    let
      val t' = subst_rterm_of' (strip_comb t);
    in if t aconv t'
      then NONE
      else SOME t'
    end;
  fun check_rterm_of ts ctxt =
    let
      val ts' = map subst_rterm_of'' ts;
    in if exists is_some ts'
      then SOME (map2 the_default ts ts', ctxt)
      else NONE
    end;
in
  Context.theory_map (Syntax.add_term_check 0 "rterm_of" check_rterm_of)
end;
*}

end
