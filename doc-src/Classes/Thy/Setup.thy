theory Setup
imports Main Code_Integer
uses
  "../../antiquote_setup.ML"
  "../../more_antiquote.ML"
begin

setup {* Code_Target.set_default_code_width 74 *}

syntax
  "_alpha" :: "type"  ("\<alpha>")
  "_alpha_ofsort" :: "sort \<Rightarrow> type"  ("\<alpha>()\<Colon>_" [0] 1000)
  "_beta" :: "type"  ("\<beta>")
  "_beta_ofsort" :: "sort \<Rightarrow> type"  ("\<beta>()\<Colon>_" [0] 1000)

parse_ast_translation {*
  let
    fun alpha_ast_tr [] = Syntax.Variable "'a"
      | alpha_ast_tr asts = raise Syntax.AST ("alpha_ast_tr", asts);
    fun alpha_ofsort_ast_tr [ast] =
      Syntax.Appl [Syntax.Constant @{syntax_const "_ofsort"}, Syntax.Variable "'a", ast]
      | alpha_ofsort_ast_tr asts = raise Syntax.AST ("alpha_ast_tr", asts);
    fun beta_ast_tr [] = Syntax.Variable "'b"
      | beta_ast_tr asts = raise Syntax.AST ("beta_ast_tr", asts);
    fun beta_ofsort_ast_tr [ast] =
      Syntax.Appl [Syntax.Constant @{syntax_const "_ofsort"}, Syntax.Variable "'b", ast]
      | beta_ofsort_ast_tr asts = raise Syntax.AST ("beta_ast_tr", asts);
  in
   [(@{syntax_const "_alpha"}, alpha_ast_tr),
    (@{syntax_const "_alpha_ofsort"}, alpha_ofsort_ast_tr),
    (@{syntax_const "_beta"}, beta_ast_tr),
    (@{syntax_const "_beta_ofsort"}, beta_ofsort_ast_tr)]
  end
*}

end